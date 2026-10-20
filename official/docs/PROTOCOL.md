# Async Swap v2 protocol

This document describes the official Async Swap v2 protocol as implemented in `official/src`. That code is
the `asyncswap/v2` draft (its external interface, contracts and tests) plus the two improvements accepted
in decision 9. This document is written from two companions and uses their names throughout:

- [STATE_MACHINE.md](STATE_MACHINE.md): states `S.*`, transitions `T.*`, shared bodies `B.*`, invariants
  `I.*`, the confidence table (§4) and the list of missing theorems. It is the reference for every name
  used here.
- [diagrams.md](diagrams.md): sequence, state and money-flow diagrams, drawn from the same names.

Where this document and an older one disagree, this document is correct. The older documents are
`v2/README.md`, `v2/docs/order-lifecycle.md`, `contract-call-sequences.md` and `price-key-crossing.md`;
`historical-matching-diagrams.md` is historical only.

**Status.**

| Check | Result |
| --- | --- |
| v2's own test suite against `official/src` | 146 passed, 1 skipped |
| `official/test/Improvements.t.sol` | 5 passed |
| Hook runtime size | 24,076 bytes, under the EIP-170 limit of 24,576 |
| Lean proofs (`lake build`) | no `sorry`, no extra axioms |

The theorems are about the Lean model. That `official/src` refines the model is supported by tests, not
proved.

---

## 1. Overview

Async Swap is a Uniswap v4 hook. It turns every exact-input swap into an **escrowed limit order** that
rests in an on-chain order book. Orders are matched by **price-time priority**. A resting order is closed
in one of four ways:

- it matches orders on the other side of the book;
- a filler fills it;
- it fills from the pool's own LP liquidity;
- the maker cancels it.

**Why limit orders on v4.** A plain v4 swap executes immediately against the pool curve, at whatever price
the curve gives. Async Swap uses `beforeSwap` with a return delta to take the whole input before the curve
runs, so the pool never trades it at market. The maker states a minimum output, which is the limit price.
The order executes only when a counterparty, a filler or the pool meets that limit. All value stays inside
the PoolManager: escrow is held as the hook's ERC-6909 claims, and every action settles inside one
`PoolManager.unlock`. See [diagrams.md §1](diagrams.md#1-components-and-actors).

**Actors**

| Actor | Role |
| --- | --- |
| Maker | Opens orders (`T.swap`, or `T.swapWithSig` through a relayer), reprices them (`T.updatePrice`) and cancels them (`T.cancelOrder`). |
| Executor | An address the maker authorizes for one pool with `T.setExecutor`. This is normally the Router. Creates, fills and Router cancels go through an executor. |
| Relayer | Submits a maker's signatures: `T.swapWithSig`, `T.cancelWithSig`, `T.updatePriceWithSig`, `T.setExecutorWithSig`. |
| Filler | Pays an order's live minimum plus the protocol fee, and receives the order's whole input (`T.fillOrder`). |
| Keeper | Anyone. Clears a crossed book (`T.matchBook`) or retries an order against pool liquidity (`T.fillFromPoolLiquidity`). |
| LP | Provides ordinary v4 liquidity. LPs are part of the environment, not the protocol. They earn the 0.30% LP fee on pool fills and receive donated bids. |
| Owner | The hook owner, transferred in two steps. Sets each pool's ordering mode, sweeps the hook's own balance, and collects from the FeeVault. |

**Contracts.**

| Contract | Role |
| --- | --- |
| `AsyncSwap` | The hook. |
| `Router` | Entry points and the unlock callback. |
| `FeeVault` | Created by the hook. `collect` is authorized by `hook.owner()`. |
| `NativeClaims` | Redeems ETH claims. |
| `AsyncMatching` | External library, linked in and run in the hook's context. |
| `AsyncFiller` | Internal library. |
| `RadixPriceTree` | Internal library. |
| `OrderSignatures` | Internal library. |

---

## 2. Concepts

The full state is in [STATE_MACHINE §1](STATE_MACHINE.md#1-state).

**Numeraire `N`.** One deployment fixes one numeraire: the chain's USDC (`AsyncSwap.numeraire`).

- The constructor rejects an address with no code (`InvalidNumeraire`). So native ETH may be traded, but it
  can only be `currency0` and is never `N`.
- `T.initialize` accepts a pool only if it holds `N` on either side (`NumeraireRequired`) and uses the
  dynamic-fee flag (`DynamicFeeRequired`). The flag lets the hook set the LP fee, and keeps a pair from being
  split across fee tiers.

**Order.** The order is the v2 struct `AsyncOrder{key, owner, zeroForOne, amountIn, amountOutMin,
priorityFee, sqrtPrice, salt}`. The hook stores, per order:

- `owner`, `amountIn`, `amountOutMin`;
- the price key, `isBuy`, `zeroForOne`;
- `sequence`, `priorityFee`, `priorityKey`;
- the FIFO links.

`amountIn` is the remaining escrowed input. A value of `0` means the slot is free (`S.Free`).

**Order id and `S.salt`.** The id is `keccak256(abi.encode(chainId, poolId, owner, zeroForOne, salt))`. The
salt is resolved at create time:

- **`T.swap`.** The Router appends `order.salt` as a fifth `hookData` word after the unchanged 4-field
  `UserParams`. `_beforeSwap` reads that word if `hookData` is at least 160 bytes, and treats a shorter
  `hookData` as `0`. A non-zero maker salt is used as given, so the maker knows the id before sending. A
  salt of `0` keeps v2's derivation:
  `keccak256(block.timestamp, block.number, msg.sender, owner, amountIn, amountOutMin, priorityFee)`.
- **`T.swapWithSig`.** The salt is always derived. The Router passes `0` and ignores `order.salt`, because
  the Permit2 witness does not cover the salt.
- **Walk.** While the id is open, the hook sets `salt = keccak256(salt)` (`I.SaltFree`).
  `AsyncOrderCreated` emits the final salt, and later calls pass it back in `order.salt`.

A closed slot is `S.Free` again, so the same salt can reopen it. Nobody can occupy another maker's ids,
because a create for `owner` needs an executor that `owner` granted.

**Sides.** An order is a **buy** when its input is `N`, and a **sell** otherwise. The side does not depend
on `zeroForOne`, which is why `N` may sit on either side of the pool.

**Price key.** A `uint128` key, WAD-scaled, in `N` per asset, computed from raw amounts:

| Side | Key |
| --- | --- |
| Buy | `floor(amountIn·1e18 / amountOutMin)` |
| Sell | `floor(amountOutMin·1e18 / amountIn)` |

The key is clamped to `[1, 2^128−1]`. The best bid is the highest key and the best ask the lowest. The cross
test is v2's `_crosses`:

- different keys cross when `buyKey > sellKey`;
- equal keys cross when `mulDiv(buyIn, sellIn, sellMin) ≥ buyMin`, and an exact tie crosses.

The cross test only filters which pairs are attempted. Safety comes from `_matchAmounts` (`I.MakerLimit`).

**Ordering modes.** A pool is `FIFO` (the default) or `PriorityFee`. `T.setOrderingMode` changes it only
while the pool's book is empty. Price comes first. Within a price level:

- FIFO orders by sequence;
- PriorityFee orders by the higher remaining bid, then by sequence, using the radix tree over
  `priorityKey = (bid << 64) | (2^64−1 − sequence)` (decision 1).

See [diagrams.md §8](diagrams.md#8-matching-priority-ipriority-and-the-cross-test).

**Priority bids.** A bid is paid in USDC.

| Mode | Bid rule |
| --- | --- |
| FIFO | must be `0`, else `InvalidOrderingModeChange` |
| PriorityFee | at least `100_000` ($0.10, else `PriorityFeeTooSmall`) and at most `2^64−1` (else `PriorityFeeTooLarge`) |

A bid buys rank within this book only. It does not buy block inclusion. It is **never refunded**. Every
settled share goes through `B.settleBid`: it is donated to LPs active at the current tick, or forfeited to
the FeeVault if there is no active liquidity.

**Sequences.** `sequence = ++nextSequence` is assigned:

- on create;
- on every reprice;
- on a partial match that changes the price key (decision 7).

A fresh sequence sorts after every live one. A partial match that keeps the key keeps the sequence. In
PriorityFee mode a reduced bid is re-indexed with the same sequence.

**Escrow.** The hook holds no order value in its own token balance.

- **At create.** `_beforeSwap` takes the input, and the bid, as hook claims (`I.Escrow`, `I.BidEscrowed`).
- **On exit.** Every exit from `S.Open` burns exactly the order's remaining escrow, through `B.payOut`,
  `B.settleBid` or `B.poolFill`.
- **Payouts.** ERC-20 payouts are tokens. Native payouts are ETH claims (id 0), redeemed through `T.redeem`.
  No settlement path calls a native recipient.

---

## 3. Order lifecycle

An order is in `S.Free`, `S.Open` or `S.Closed`. `S.Closed` is labelled `Matched`, `Filled`, `PoolFilled`
or `Cancelled`, and uses the same storage as `S.Free`. See
[STATE_MACHINE §2.1](STATE_MACHINE.md#21-per-order-states) and
[diagrams.md §7](diagrams.md#7-per-order-states-sfree-sopen-sclosed).

| From | To | By |
| --- | --- | --- |
| `S.Free` | `S.Open` | `T.swap`, `T.swapWithSig` |
| `S.Open` | `S.Open` | `B.reduceSide` partial; `T.updatePrice` / `T.updatePriceWithSig` |
| `S.Open` | `S.Closed` (Matched) | `B.matchLoop` exhausts the input or the minimum |
| `S.Open` | `S.Closed` (Filled) | `T.fillOrder` |
| `S.Open` | `S.Closed` (PoolFilled) | `B.poolFill`, in `T.swap` or `T.fillFromPoolLiquidity` |
| `S.Open` | `S.Closed` (Cancelled) | `T.cancelOrder` / `T.cancelWithSig` |

The Lean model collapses these states to `absent` and `open_`. `step_lifecycle` (v1 model) proves that no
other transitions exist.

Each step below runs inside one `unlock`, using the transaction phases in
[STATE_MACHINE §2.2](STATE_MACHINE.md#22-transaction-phases-one-poolmanagerunlock). The money flow for every
step is in [diagrams.md §9](diagrams.md#9-money-flow-per-currency-and-the-invariants).

### 3.1 Setup

The maker grants the Router as executor in one of two ways:

- `T.setExecutor(poolId, router, true)`;
- `T.setExecutorWithSig`, either on its own or as the `ExecutorGrant` of the maker's first `T.swapWithSig`.

The maker also needs these approvals:

| Payment | Approve |
| --- | --- |
| ERC-20 input on `T.swap` | the Router |
| ERC-20 input on `T.swapWithSig` | Permit2 |
| A non-zero bid | the Router, for USDC, on either path |

### 3.2 Create: `T.swap`

See [diagrams.md §2](diagrams.md#2-tswap-create-bid-escrow-matchneworder-pool-fallback).

1. **Router checks.**
   - `order.owner == msg.sender`.
   - `userData` decodes to `UserParams{user, executor, amountOutMin, priorityFee}`, and `user`, `executor`
     (the Router), the minimum and the bid each equal the order's.
   - Native input requires `msg.value == amountIn`. ERC-20 input requires `msg.value == 0`.
2. **`PoolManager.swap(key, −amountIn, sqrtPrice, hookData = UserParams ‖ makerSalt)`.**
3. **`_beforeSwap`.**
   - Checks: exact input (`ExactInputOnly`); `sender == executor` and `isExecutor[user][executor]`
     (`NotAuthorizedExecutor`); `amountIn > 0` and `amountOutMin > 0` (`ZeroAmount`).
   - `take(in, hook, amountIn, claims)`: the input becomes a hook claim.
   - `_createOrder`: resolves `S.salt`, checks the bid rule, stores the order (`S.Free` → `S.Open`,
     `sequence = ++nextSequence`), appends it to its level, records the pending match id, and emits
     `AsyncOrderCreated` with the final salt.
   - If the bid is `f > 0`: `numeraire.take(hook, f, claims)`. The bid becomes a hook claim in the same
     unlock (decision 9).
   - Emits `HookSwap`, then returns `BeforeSwapDelta(+amountIn, 0)` so the curve does not move.
4. **Funding.** The Router settles the input:
   - ERC-20: `transferFrom(maker)`.
   - Native: the forwarded `msg.value`.

   Then `_settlePriorityFee`: `sync(N)`, `safeTransferFrom(maker → PM, f)`, `settleFor(hook)`. Nothing else is
   needed. An unpaid bid leaves the hook's delta at `−f`, and the unlock reverts.
5. **`matchNewOrder(order)`.** Consumes the pending id, then runs `B.matchLoop` on the new order for at most
   8 pairs (§3.3).
6. **Pool fallback** (decision 10). If the order is still `S.Open`, the hook runs
   `try this.fillOrderFromPoolLiquidity(order, id)`, which is `B.poolFill` (§3.5). A revert rolls back only
   that attempt; earlier matches and the open remainder stay.
7. **`I.DeltaZero`.** Every locker delta is `0`, or the whole transaction reverts.

**Money flow.** The maker pays `amountIn` of the input, plus `f` USDC. The hook's claims grow by exactly
those amounts (`created_order_escrowed`).

### 3.3 Match: `B.matchLoop` (inside `T.swap`, or `T.matchBook`)

See [diagrams.md §5a](diagrams.md#5a-tmatchbook-by-a-keeper) and
[STATE_MACHINE §2.3](STATE_MACHINE.md#23-shared-bodies). Each iteration:

1. Takes the best opposite level, picks its head under the ordering mode, and stops unless `_crosses` holds.
2. **`B.matchPair`.** The older order (lower sequence) rests, and its limit sizes the trade
   (`_matchAmounts`). For a resting buy:
   - `quote = min(sellIn·buyIn/buyMin, buyIn)`;
   - `asset = ceil(quote·buyMin/buyIn)`;
   - the trade requires `asset ≤ sellIn` and `quote ≥ ceil(asset·sellMin/sellIn)`.

   A resting sell is the mirror image. A zero amount means no match, and the loop stops. A match charges no
   protocol fee. Emits `AsyncOrdersMatched`.
3. **`B.reduceSide`**, run on each order:
   - `B.payOut` sends the used input to the counterparty.
   - `B.settleBid` settles `floor(bid·used/amountIn)`.
   - The order's input, minimum and bid are reduced.
   - If the remaining input or the remaining minimum is `0`, the order goes to `S.Closed` (Matched):
     `B.settleBid` settles the rest of the bid and `B.payOut` refunds the unused input.
   - Otherwise the order stays `S.Open` with a new key. If the key changed it gets a new sequence; in
     PriorityFee mode a lower bid is re-indexed.

`T.matchBook(key, maxMatches)` runs the same loop on the best bid against the best ask, for 1 to 8 pairs
(`InvalidMatchBound` otherwise). It has no pool fallback.

### 3.4 Fill: `T.fillOrder`

See [diagrams.md §3](diagrams.md#3-tfillorder-with-fee-flows).

1. **Live price.** `live = m + fee(m)`, where `m` is the stored `amountOutMin`. Storage is read, not
   calldata. The fill requires `live ≤ maxPrice` ("Price exceeds maxPrice"), which protects the filler
   against a reprice front-run.
2. **Output payment.**
   - Native output: `msg.value == live`. The ETH is forwarded to the hook before the unlock, and the hook
     spends only this transient deposit (`UnaccountedNativeOutput`).
   - ERC-20 output: `sync`, `safeTransferFrom(filler → PM, live)`, then `settleFor(hook)`.
3. **`executeOrder`.** Requires the Router to be the maker's executor (`NotAuthorizedExecutor`) and the
   order to be open (`OrderNotFound`). Then:
   - the maker receives exactly `m`;
   - the FeeVault receives `fee` as a claim (`OrderFeeAccrued`);
   - `B.payOut` sends the filler the whole `amountIn`;
   - `B.settleBid` settles the whole bid;
   - the order moves to `S.Closed` (Filled), and `AsyncOrderFilled` is emitted.

Fills are for the whole order and do not follow book priority.

### 3.5 Pool fill: `B.poolFill` (the `T.swap` fallback, or `T.fillFromPoolLiquidity`)

See [diagrams.md §4](diagrams.md#4-tfillfrompoolliquidity-bpoolfill-with-the-030-override).

`T.fillFromPoolLiquidity` calls `tryFillOrderFromPoolLiquidity`, which:

- requires the Router to be the maker's executor;
- wraps the self-call `fillOrderFromPoolLiquidity` in `try/catch`;
- returns `false` and leaves the order `S.Open` if the self-call fails. The outer transaction still commits.

The self-call (`NotSelf` unless the hook calls itself) does the following:

1. Requires active liquidity (`NoActiveLiquidity`).
2. Burns the input claim.
3. Sets the dynamic LP fee to `3000` (0.30%).
4. Swaps the whole input with no price limit, then restores the previous LP fee. The hook is the swap's
   sender, so its own `beforeSwap` is skipped and no order is created.
5. Requires that all input was used (`PartialLiquidityFill`) and that the output `y ≥ minOut`
   (`LimitPriceNotMet`).
6. Pays the maker the **full** `y`.
7. Runs `B.settleBid` on the whole bid.
8. Moves the order to `S.Closed` (PoolFilled) and emits `AsyncOrderLiquidityFilled`.

### 3.6 Cancel: `T.cancelOrder` / `T.cancelWithSig`

See [diagrams.md §5b](diagrams.md#5b-tcancelorder-with-bsettlebid) and
[§6](diagrams.md#6-signed-flows-tswapwithsig-and-tcancelwithsig).

The Router accepts a cancel from the owner ("Only owner can cancel"), or with a valid `CancelOrder` signature
(`T.cancelWithSig`). The hook accepts the owner or a granted executor (`NotAuthorizedExecutor`). This lets a
smart-contract maker cancel from its own unlock.

The hook then:

- refunds the whole remaining `amountIn` through `B.payOut`;
- runs `B.settleBid` on the whole remaining bid, which is not refunded;
- moves the order to `S.Closed` (Cancelled) and emits `AsyncOrderCancelled`.

### 3.7 Reprice: `T.updatePrice` / `T.updatePriceWithSig`

Only the owner can reprice (`NotOrderOwner`), directly or with an `UpdatePrice` signature. The new minimum
must be non-zero (`ZeroAmount`).

A reprice gives the order a new key and a new sequence, and appends it at the back of its level. It emits
`AsyncOrderPriceUpdated`.

It uses no unlock and moves no ledger. It also does not trigger matching: a crossing reprice waits for the
next `T.swap` or `T.matchBook`.

### 3.8 Native ETH

- **Native input.** `T.swap` only, with `msg.value == amountIn`.
- **Native fill output.** Paid as the exact `msg.value`, checked against the hook's transient
  `PENDING_NATIVE_DEPOSIT` ledger.
- **Native proceeds and refunds.** Paid as claim id 0. `T.redeem` burns the caller's claims and takes ETH
  to the recipient in one unlock. Before redeeming, the holder approves `NativeClaims` for id 0 on the
  PoolManager.

---

## 4. Entry points

These are v2's signatures. The guards, effects and provenance of each transition are in
[STATE_MACHINE §2.4](STATE_MACHINE.md#24-entry-points) under the `T.*` name shown.

### Router (EIP-712 `"AsyncSwap Router","1"`)

| T.* | Signature | Caller | Effect | Reverts | Diagram |
| --- | --- | --- | --- | --- | --- |
| `T.swap` | `swap(AsyncOrder order, bytes userData) payable` | maker | create, then `B.matchLoop` (≤ 8), then `B.poolFill` fallback | "Only owner can swap", "user mismatch", "Use router as your executor!", "amountOutMin mismatch", "priorityFee mismatch", "msg.value != order.amountIn", "msg.value forbidden for ERC20 input"; hook: `ExactInputOnly`, `NotAuthorizedExecutor`, `ZeroAmount`, `InvalidOrderingModeChange`, `PriorityFeeTooSmall`, `PriorityFeeTooLarge` | [§2](diagrams.md#2-tswap-create-bid-escrow-matchneworder-pool-fallback) |
| `T.swapWithSig` | `swapWithSig(AsyncOrder order, PermitData permit, ExecutorGrant grant)` | relayer | as `T.swap`; input through the Permit2 witness; salt always derived; optional grant first | "Native input needs swap()"; Permit2 errors; grant errors; hook errors as above | [§6](diagrams.md#6-signed-flows-tswapwithsig-and-tcancelwithsig) |
| `T.fillOrder` | `fillOrder(AsyncOrder order, uint256 maxPrice, bytes data) payable` | filler | whole-order fill at `live = m + fee(m)` | "Price exceeds maxPrice", "msg.value != livePrice", "msg.value forbidden for ERC20 output", "Native output transfer to hook failed"; hook: `NotAuthorizedExecutor`, `OrderNotFound`, `UnaccountedNativeOutput` | [§3](diagrams.md#3-tfillorder-with-fee-flows) |
| `T.cancelOrder` | `cancelOrder(AsyncOrder order)` | maker | refund input, settle bid | "Only owner can cancel"; hook: `NotAuthorizedExecutor`, `OrderNotFound` | [§5b](diagrams.md#5b-tcancelorder-with-bsettlebid) |
| `T.cancelWithSig` | `cancelWithSig(AsyncOrder order, uint256 nonce, uint256 deadline, bytes signature)` | relayer | signed cancel; the nonce is burnt before the signature check | `SignatureExpired`, `NonceAlreadyUsed`, `InvalidSignature`; hook errors as for `T.cancelOrder` | [§6](diagrams.md#6-signed-flows-tswapwithsig-and-tcancelwithsig) |
| `T.matchBook` | `matchBook(PoolKey key, uint8 maxMatches)` | anyone | `B.matchLoop`, best bid against best ask | `InvalidMatchBound` | [§5a](diagrams.md#5a-tmatchbook-by-a-keeper) |
| `T.fillFromPoolLiquidity` | `fillFromPoolLiquidity(AsyncOrder order)` | anyone | `B.poolFill`; a failed attempt leaves the order open | `NotAuthorizedExecutor`, `OrderNotFound` | [§4](diagrams.md#4-tfillfrompoolliquidity-bpoolfill-with-the-030-override) |
| | `unlockCallback(bytes)` | PoolManager | dispatches the action | "Caller is not PoolManager" | |
| | views: `DOMAIN_SEPARATOR()`, `cancelNonceUsed(maker, nonce)`, `PERMIT2()` | | | | |

### AsyncSwap hook (EIP-712 `"AsyncSwap","1"`)

| T.* | Signature | Caller | Effect | Reverts |
| --- | --- | --- | --- | --- |
| `T.initialize` | `beforeInitialize` (callback) | PoolManager | new empty FIFO book | `NumeraireRequired`, `DynamicFeeRequired` |
| part of `T.swap` | `beforeSwap` (callback) | PoolManager | input and bid claims, `_createOrder` | as `T.swap` |
| part of `T.swap` | `matchNewOrder(AsyncOrder order) returns (uint8)` | the creating executor, in the same unlock | `B.matchLoop`, then the fallback | `NotAuthorizedExecutor`, `OrderNotFound` |
| `T.matchBook` | `matchBook(PoolKey key, uint8 maxMatches) returns (uint8)` | anyone, inside an unlock | `B.matchLoop` | `InvalidMatchBound` |
| `T.fillOrder` | `executeOrder(AsyncOrder order, bytes data)` | the maker's executor, inside an unlock | fill; `data = abi.encode(filler)` | `NotAuthorizedExecutor`, `OrderNotFound`, `UnaccountedNativeOutput` |
| `T.cancelOrder` | `cancelOrder(AsyncOrder order)` | owner or executor, inside an unlock | cancel | `NotAuthorizedExecutor`, `OrderNotFound` |
| `T.fillFromPoolLiquidity` | `tryFillOrderFromPoolLiquidity(AsyncOrder order) returns (bool)` | the maker's executor, inside an unlock | guarded `B.poolFill` | `NotAuthorizedExecutor`, `OrderNotFound` |
| `B.poolFill` | `fillOrderFromPoolLiquidity(AsyncOrder order, bytes32 id)` | the hook itself | pool fill; reverts as a unit | `NotSelf`, `NoActiveLiquidity`, `PartialLiquidityFill`, `LimitPriceNotMet` |
| `T.updatePrice` | `updatePrice(AsyncOrder order, uint256 newAmountOutMin)` | owner | reprice, new sequence | `NotOrderOwner`, `ZeroAmount`, `OrderNotFound` |
| `T.updatePriceWithSig` | `updatePriceWithSig(AsyncOrder order, uint256 newAmountOutMin, uint256 nonce, uint256 deadline, bytes signature)` | relayer | signed reprice | `SignatureExpired`, `NonceAlreadyUsed`, `InvalidSignature`, then as `T.updatePrice` |
| `T.setExecutor` | `setExecutor(PoolId poolId, address executor, bool allow)` | maker | grant or revoke | none |
| `T.setExecutorWithSig` | `setExecutorWithSig(PoolKey key, address maker, address executor, bool allow, uint256 nonce, uint256 deadline, bytes signature)` | relayer or Router | signed grant | `SignatureExpired`, `NonceAlreadyUsed`, `InvalidSignature` |
| `T.invalidateNonce` | `invalidateNonce(uint256 nonce)` | any signer | burn a hook nonce | `NonceAlreadyUsed` |
| `T.setOrderingMode` | `setOrderingMode(PoolKey key, OrderingMode mode)` | owner | FIFO or PriorityFee; empty book only | `NotOwner`, `InvalidOrderingModeChange` |
| `T.sweep` | `sweep(Currency currency, address to)` | owner | move the hook's own balance; never claims | `NotOwner`, `ZeroAddress` |
| `T.transferOwnership` / `T.acceptOwnership` | `transferOwnership(address)` / `acceptOwnership()` | owner / nominee | two-step ownership transfer | `NotOwner`, `ZeroAddress` |
| | `receive()` | Router, on native fills | credit `PENDING_NATIVE_DEPOSIT` | none |

Hook views: `asyncOrder`, `asyncOrderInfo`, `asyncOrderPriorityFee`, `orderingMode`, `bestOrder`,
`orderBookLevel`, `orderBookOrder`, `isExecutor`, `calculateHookFee` (always `0`), `calculatePoolFee`,
`nonceUsed`, `numeraire`, `feeVault`, `owner`, `pendingOwner`, `DOMAIN_SEPARATOR`.

v2's `recordPriorityFee` is removed, together with the `priorityFeeEscrowed` field and the
`PriorityFeeNotEscrowed` error.

Hook permissions are `beforeInitialize`, `beforeAddLiquidity` (a no-op that returns its selector),
`beforeSwap` and `beforeSwapReturnDelta`.

### NativeClaims and FeeVault

| T.* | Signature | Caller | Effect | Reverts |
| --- | --- | --- | --- | --- |
| `T.redeem` | `NativeClaims.redeem(address recipient, uint256 amount)` | holder of claim id 0 (NativeClaims approved on the PM) | burns the caller's ETH claims and takes ETH to `recipient` | `InvalidRedemption`, `ReentrantRedemption`, PM allowance and balance errors, a failed ETH transfer |
| `T.collect` | `FeeVault.collect(Currency currency, address recipient)` | `hook.owner()` | burns all of the vault's claims in `currency` and takes the tokens to `recipient` | `Unauthorized`, `ZeroAddress` |

Both contracts also have `unlockCallback(bytes)`, callable only by the PoolManager.

**Events.** These keep v2's names:

- `AsyncOrderCreated`, which carries the final salt;
- `AsyncOrderPriceUpdated`, `AsyncOrderFilled`, `AsyncOrderCancelled`, `AsyncOrdersMatched`,
  `AsyncOrderLiquidityFilled`;
- `OrderFeeAccrued`, `PriorityFeeDonated`, `PriorityFeeForfeited`, `OrderingModeChanged`;
- `ExecutorSet`, `NonceInvalidated`, `OwnershipTransferStarted`, `OwnershipTransferred`, `Swept`;
- `HookSwap`;
- `NativeRedeemed`, `FeesCollected`.

---

## 5. Fees and bids

| What | Amount | Paid by | To |
| --- | --- | --- | --- |
| Protocol fee on `T.fillOrder` | `fee(m) = floor(3·m/997)` = 30 bps of gross `m + fee`, rounded down | filler, on top of `m` | FeeVault, as an output-currency claim |
| LP fee on `B.poolFill` | 0.30% (`3000`), set on the dynamic-fee pool for that swap, then restored | the order's input, inside the swap | in-range LPs |
| Order-to-order match | none | | |
| Bid share, `B.settleBid` | `floor(bid·used/amountIn)` per match; the whole remaining bid on Matched close, Filled, PoolFilled or Cancelled | maker, escrowed at create | donated to active LPs, or forfeited to the FeeVault if there is no liquidity |

`calculatePoolFee` uses the split form `(n/997)·3 + ((n%997)·3)/997` so that it cannot overflow.

A partial match can leave a remaining bid below the $0.10 creation minimum. The order then ranks by that
smaller bid.

The FeeVault holds only fees and forfeited bids. `T.collect` cannot reach the escrow, because the escrow is
held as the hook's claims, not the vault's.

---

## 6. Signatures and Permit2

| Domain | Name, version | Verifies | Nonces |
| --- | --- | --- | --- |
| Hook | `"AsyncSwap","1"` | `SetExecutor`, `UpdatePrice` | `AsyncSwap.nonceUsed` |
| Router | `"AsyncSwap Router","1"` | `CancelOrder` | `Router.cancelNonceUsed` |
| Permit2 | Permit2's own | `PermitWitnessTransferFrom` with the `AsyncOrder` witness | Permit2 bitmap |

Signatures are checked with OpenZeppelin `SignatureChecker`, so EOA and ERC-1271 signers both work. Every
check enforces `deadline` and burns an unordered nonce.

Type strings, from `OrderSignatures.sol`:

```
PoolKey(address currency0,address currency1,uint24 fee,int24 tickSpacing,address hooks)
AsyncOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 amountOutMin,uint256 priorityFee,PoolKey pool)
SetExecutor(address maker,address executor,bool allow,PoolKey pool,uint256 nonce,uint256 deadline)
UpdatePrice(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 newAmountOutMin,bytes32 orderId,uint256 nonce,uint256 deadline)
CancelOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,bytes32 orderId,uint256 nonce,uint256 deadline)
Permit2 witness:  "AsyncOrder witness)" ‖ AsyncOrder(...) ‖ PoolKey(...) ‖ "TokenPermissions(address token,uint256 amount)"
```

**What each signature commits to** (`I.SigBinding`, [P1] at the Hashing layer):

- **`T.swapWithSig`** commits to the input token, `amountIn`, the spender (the Router), the Permit2 nonce and
  deadline, and the witness. The witness covers the maker, `tokenIn`, `tokenOut`, `amountIn`, `amountOutMin`,
  `priorityFee` and the pool. Because `currency0 ≠ currency1`, it also fixes the direction
  (`routerPermit_inj`, `hashOrder_inj`, `tokens_inj`).
- **The witness provably does not cover `sqrtPrice` or `salt`** (decision 6).
  - `sqrtPrice` is harmless, because the hook consumes the whole input.
  - The salt is handled in the code: `T.swapWithSig` ignores `order.salt` and always derives it, so a
    relayer cannot choose the order id.
- **`SetExecutor`** commits to the maker, the executor, `allow`, the pool, the nonce and the deadline.
- **`UpdatePrice`** commits to the maker, the tokens, the **stored** `amountIn`, the new minimum, the order
  id, the nonce and the deadline.
- **`CancelOrder`** commits to the maker, the tokens, the stored `amountIn`, the order id, the nonce and the
  deadline. The nonce is needed because ids can recur after an order closes.
- **Domain separation.** A hook signature is never valid at the Router or at Permit2, and never on another
  chain (`digest_ne_of_contract`, `digest_ne_of_chain`, `domainSeparator_inj`).
- **No replay.** A used nonce stays used (`I.NoReplay`: `verify_no_replay`, `nonce_monotone`,
  `cancelWithSig_no_replay`).

---

## 7. Guarantees

The markers come from the confidence table in [STATE_MACHINE §4](STATE_MACHINE.md#4-confidence-table):

| Marker | Meaning |
| --- | --- |
| **[P]** | Proved for the model configuration: `N = currency1`, one pool, no pool fallback, no fee override. |
| **[P1]** | Proved in the v1 model, or only in a separate Lean layer (Book, Match, Priority, Admin, Hashing, Radix). |
| **[T]** | Tested only, in `official/test`. |
| **[–]** | Not covered. |

The step theorems assume the environment hypotheses in [STATE_MACHINE §3](STATE_MACHINE.md#3-invariants):
makers, fillers and redeemers are never the hook, and the PoolManager never acts as a party.

### Invariants

| Invariant | In plain words | Status |
| --- | --- | --- |
| `I.Escrow` | The hook's claims in each currency equal the open input plus the open bids. | **[P]** `step_escrow` (with `escrow_matchLoop`, `escrow_reduceSideBody`, `escrow_closeBody`). **[T]** for the pool fallback and for `N = currency0`. |
| `I.HookClaimsNonNeg` | The hook's claims are never negative. | **[P]** `step_hook_claims_nonneg` |
| `I.Backing` | The PoolManager's balance equals the claim supply plus the pool reserves. | **[P]** `step_backing`. Across LP actions this relies on v4's own accounting (assumed). |
| `I.DeltaZero` | Every unlock nets to zero. | **[P]** `swapBody_deltasZero`, `matchBookBody_deltasZero`, `fillBody_deltasZero`, `cancelBody_deltasZero`, `liquidityFillBody_deltasZero`, `matchLoop_neutral` |
| `I.Conservation` | No action creates or destroys any currency. | **[P]** `step_conservation`. **[–]** for `T.swapWithSig`, `T.collect` and `T.sweep`. |
| `I.ClaimsNonNeg` | No claim balance goes negative. | **[P]** `step_claims_nonneg` |
| `I.BalNonNeg` | No wallet balance outside the PoolManager goes negative. | **[P]** `step_bal_nonneg`, **except** a buy-side `T.swap` with a bid (`hgap`), which is **[T]** (§9) |
| `I.BidEscrowed` | Every open order's bid is held as `claims[N][hook]`. | **[P]** at create (`created_order_escrowed`). The global form is **[–]**. **[T]** `test_bidEscrowedInCreateUnlock`. |
| `I.Settlement` | Each party gets exactly its share. The maker gets `m` and the filler gets `amountIn` on a fill; a cancel refunds exactly `amountIn`. | **[P]** `fill_settlement`, `cancel_settlement`, `redeem_settlement`. **[P1]** `fill_fee_is_30bps`, `collect_settlement`, `sweep_settlement`, `fillOrder_ignores_calldata_amounts`, `fill_native_requires_exact_value`. |
| `I.MakerLimit` | Every match honours both limit prices and both escrows. A maker closed by matches has received at least its minimum. Bids are paid pro rata and never leak. | **[P1]** `matchAmounts_sound`, `matchAmounts_cross`, `maker_limit_honored`, `runLegs_priorityFee`. **[P]** bridge: `matchLoop_head_sound`, `reduceSideBody_orders`. |
| `I.Priority` | Best price first. At the same price, FIFO or bid-then-FIFO. A reprice goes last. | **[P1]** `best_bid_is_max`, `best_ask_is_min`, `crossed_iff_best_crossed`, `bestAtPrice_priority`, `fifo_head_earliest`, `reprice_sequence_last`, `priorityKey_lt_iff`. **[T]** link to the state machine: `invariant_bestPricesAgreeWithLinearScan`, `test_priorityFeeBreaksEqualPriceTiesAfterPricePriority`. |
| `I.RadixRefines` | The storage trie implements the functional trie. | **[P1]** `best_refines`, `PriceIndex.insert_refines`, `PriceIndex.remove_refines` |
| `I.Bounds` | No `uint32` id, `uint64` sequence or `uint128` key overflows, and no `uint256` intermediate overflows, under the stated input bounds. | **[P1]** `IdAlloc.insert_no_overflow`, `IdAlloc.run_next_le_peak`, `sequence_fits_uint64`, `priceKey_mulDiv_lt`, `matchAmounts_intermediates_lt`, `donatedFee_lt_two_pow_64`, … |
| `I.NoReplay` | A signature is accepted at most once. | **[P1]** `verify_no_replay`, `verify_respects_deadline`, `nonce_monotone`, `cancelWithSig_no_replay` |
| `I.SigBinding` | A signature commits to exactly its listed fields, in one domain and on one chain. | **[P1]** §6 |
| `I.Owner` | The owner changes only through `acceptOwnership`, and only to the nominee. | **[P1]** `owner_change_only_via_accept` |
| `I.HookHoldsNoTokens` | Fills and cancels leave the hook's own balance unchanged. | **[P]** as a conjunct of `fill_settlement` and `cancel_settlement`. The step-level form is **[T]**. |
| `I.SaltFree` | A create always lands on a free id. | Assumed. **[T]** `test_makerSalt_idKnownBeforeSending`, `test_zeroSalt_keepsDerivedSalt`, `test_reusedMakerSalt_walksToAFreeId`, `test_swap_duplicateParamsTriggerSaltWalk`. |
| `I.SupplyConsistent`, `I.SupplyNonNeg`, `I.ReservesNonNeg`, `I.PmBalNonNeg` | Claim supply is the sum of claims, and supply, reserves and the PoolManager's balance are non-negative. | **[–]** |

### Per transition

Summarized from [STATE_MACHINE §4](STATE_MACHINE.md#4-confidence-table):

| Transition | Status |
| --- | --- |
| `T.fillOrder`, `T.cancelOrder`, `T.cancelWithSig`, `T.matchBook`, `T.fillFromPoolLiquidity`, `T.updatePrice`, `T.setExecutor`, `T.setOrderingMode`, `T.redeem` | **[P]** on every ledger invariant |
| `T.swap`, sell side | **[P]** |
| `T.swap`, buy side with a bid | **[P]**, except `I.BalNonNeg`, which is **[T]** |
| `T.swap`, one-step bid escrow | **[P]** through the model's two-step body. Their equivalence is **[–]**, and it is tested (**[T]**) by `test_bidEscrowedInCreateUnlock` and `test_noRecordPriorityFeeStep`. |
| `T.swap`, pool fallback | **[T]** (`test_lpLiquidityFillsOrderWhenMakerMinimumIsMet`, `test_lpPriceFailureLeavesOrderOpenAndRetryCanFill`) |
| `T.swap`, `N = currency0` | **[T]** (`test_acceptNumeraireOnEitherSortedSide`, `test_buyAssetWithSixDecimalUsdc`) |
| `T.swapWithSig`, `T.updatePriceWithSig`, `T.setExecutorWithSig`, `T.invalidateNonce`, `T.collect`, `T.sweep` | **[P1]** |
| `T.transferOwnership`, `T.acceptOwnership` | **[P1]** (Admin layer) |
| Partial-fill resequencing (decision 7) | ledgers **[P]**; the sequence rule **[T]** (`test_crossingOrdersPartiallyFillAndKeepResidualOnBook`) |
| Exact crossing on equal keys | **[T]** (`test_equalKeyNonCrossingPairDoesNotBlockMatching`, `test_exactTieExecutes`). Safety holds under any crossing rule: **[P1]** `matchAmounts_sound`. |
| 0.30% LP fee override and restore | **[–]**. The LP-fill tests exercise it but do not assert it. |
| `T.initialize` | numeraire check **[T]** (`testFuzz_rejectPairsWithoutNumeraire`); dynamic-fee check **[–]** |

### Theorems the spec still needs

These are the proposed names from
[STATE_MACHINE §4](STATE_MACHINE.md#theorems-the-spec-still-needs):

1. `step_bal_nonneg` without `hgap`. Strengthen `swapGuard` to require `amountIn + priorityFee ≤ bal N owner`.
2. `bid_escrowed_at_create` (the one-step create equals `createBody` followed by `priorityFeeBody`) and
   `step_all_escrowed`. Alternatively, drop `escrowed` and re-prove `I.Escrow`.
3. `salt_walk_free`, `salt_zero_derivation`, `maker_salt_id`, `swap_sig_ignores_salt`.
4. Numeraire on either side: make `numeraire` a `Config` field and re-prove the `step_*` theorems.
5. Pool fallback in create: `swap_fallback_escrow`, `swap_fallback_backing`, `swap_fallback_deltasZero`,
   `poolFallback_atomic`.
6. `liquidityFill_lp_fee`, `liquidityFill_restores_lp_fee`.
7. `reduce_resequence_last`, `reduce_keeps_sequence`. These need `sequence` in `V2.World`.
8. `matchLoop_follows_book`, which links `I.Priority` to the state machine.
9. `matchGuard_iff_crosses`, for v2's exact crossing rule.
10. `step_supply_eq_sum`, `step_reserves_nonneg`, `step_pm_bal_nonneg`.
11. Signed and admin actions in `V2.step`, with the `step_*` theorems extended over them.
12. `step_hook_bal_unchanged`, `fill_pending_reset`.

---

## 8. Decisions

| # | Date | Decision |
| --- | --- | --- |
| 1 | 2026-10-15 | Same-price priority: in PriorityFee mode a higher bid wins, then FIFO; in FIFO mode, sequence only. A reprice goes to the back. |
| 2 | 2026-10-15 | Arithmetic: unbounded ℕ/ℤ with explicit per-site bounds. |
| 3 | 2026-10-15 | The call-sequence state machine is extended to v2. |
| 4 | 2026-10-15 | The periphery is in scope: radix storage, the native ledger, EIP-712 and Permit2 hashing, `collect`, `sweep`. |
| 5 | 2026-10-16 | Radix node ids: freed ids are recycled; ids stay `uint32`. |
| 6 | 2026-10-16 | keccak is modelled symbolically and assumed collision-free. `sqrtPrice` and `salt` are outside the Permit2 witness. |
| 7 | 2026-10-17 | A partial fill that changes the price key gets a new sequence. |
| 8 | 2026-10-17 | Stay compatible with v2: domains `"AsyncSwap","1"` and `"AsyncSwap Router","1"`, the `HookSwap` event, and v2's interface and tests. |
| 9 | 2026-10-17 | Adopt the rebuild's improvements: the bid is escrowed in the create unlock, the maker chooses the salt (walked if taken, final salt emitted), and tests are named after theorems. |
| 10 | 2026-10-17 | Follow v2: `N` may be on either side; pools need USDC and the dynamic-fee flag; pool fills charge 0.30%; a new order falls back to pool liquidity after matching. |

### Official vs the v2 draft

The interface and events match v2's. The differences are the two improvements in decision 9 and one bug fix
([STATE_MACHINE §5](STATE_MACHINE.md#5-official-vs-v2-draft-and-vs-the-proofs-only-rebuild)):

1. **The bid is escrowed at create.**
   - `_beforeSwap` takes the bid claim.
   - `Router._settlePriorityFee` only pays the bid in.
   - `recordPriorityFee` (in the hook, `AsyncMatching` and `AsyncFiller`), `priorityFeeEscrowed`, the
     `PriorityFeeNotEscrowed` error and its five checks are all removed.
2. **The maker chooses the salt.**
   - The salt travels as a fifth `hookData` word on `T.swap`.
   - `0`, or a 4-word `hookData`, keeps v2's derivation.
   - `T.swapWithSig` always derives the salt.
   - `UserParams` is unchanged, so v2's tests still compile and pass.

3. **A bug fix.** After a FIFO reprice, v2 left the order's stale `next` pointer, which later corrupted the
   price-level lists (a cancelled order as best, a crossed book that could not be matched, new orders at that
   price reverting). `AsyncFiller._append` now clears it. Found by the proof-derived invariant tests; see
   [STATE_MACHINE §5](STATE_MACHINE.md#5-official-vs-v2-draft-and-vs-the-proofs-only-rebuild).

### Official vs the proofs-only rebuild

`rebuild/` was written from the Lean model alone, and is a separate artifact, not the official code. Its
differences from the official protocol are listed in
[STATE_MACHINE §5](STATE_MACHINE.md#5-official-vs-v2-draft-and-vs-the-proofs-only-rebuild).

### Rejected in cycle 1

- **Matching other users' orders in `afterSwap`.** By then `beforeSwap` has consumed the swap, so
  `afterSwap` sees an empty swap. It also runs before the maker has paid. The idea would add gas and a
  re-entrancy surface, and changing the permission flags would change the hook address.
- **Paying MEV in `afterSwap`.** Rejected for the same reasons.

### Open ideas

- A priority-fee MEV tax on fills and matches, for chains ordered by priority fee (Unichain, OP stack).
- A keeper reward for `T.matchBook`, paid from the crossing spread.

---

## 9. Known gaps and open questions

**Model gaps.** The full list is under "Theorems the spec still needs" (§7).

- **Numeraire fixed to `currency1`.** The model fixes `numeraire := currency1`. The code accepts `N` on
  either side, and `N = currency0` is **[T]** only.
- **Pool fallback and fee override.** The model does not include the fallback after matching, or the 0.30%
  override and restore. `liquidityFillBody` takes the pool output `y` as an input that satisfies the
  contract's checks.
- **`I.BalNonNeg` gap (`hgap`).** A buy-side `T.swap` with a bid takes USDC from the maker twice: first
  `amountIn`, then the bid. `swapGuard` (`AsyncSwapProtocol/V2/Model.lean`) checks each debit against the
  starting balance on its own, never their sum. So `step_bal_nonneg` excludes this case. The Solidity is
  safe: the second `safeTransferFrom` reverts on an insufficient balance, and an unpaid bid would also leave
  the hook's delta unsettled.
- **Bid escrow and maker salt (decision 9).** The model still runs the bid escrow in two steps
  (`priorityFeeBody`), and treats the salt walk as the assumption "the slot is free". Both are **[T]** in
  `official/src`.
- **Abstractions in the model.** The choice of match is an input to the model (see `I.Priority`).
  Signatures are an oracle. Events, gas and revert reasons are not modelled.

**Open questions.**

- **Revoking a signed cancel.** `Router.cancelNonceUsed` has no `invalidate` function, so a maker cannot
  revoke a signed `CancelOrder` that has not been submitted, except by cancelling the order directly.
- **Salt and the Permit2 witness.** The witness does not cover the salt. This is mitigated: `T.swapWithSig`
  ignores `order.salt` and always derives it, so a signed order's id is fixed by the block and the order
  fields, not by the relayer. A maker who needs a predictable id must use `T.swap`.
- **Saturated keys.** Distinct prices that saturate to the same boundary key (`1` or `2^128−1`) fall back to
  sequence order among themselves.
- **Fills bypass priority.** `T.fillOrder` and `T.fillFromPoolLiquidity` target one order and skip book
  priority. This is by design.
- **Crossing reprices wait.** A reprice that crosses the book does not match until the next `T.swap` or
  `T.matchBook`.
