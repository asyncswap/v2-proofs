# Async Swap v2: protocol diagrams

These diagrams draw the **official protocol** as implemented in `official/src`: v2's code and external
interface, plus the two improvements from decision 9. Every state (`S.*`), transition (`T.*`), shared body
(`B.*`) and invariant (`I.*`) uses the reference names in [`STATE_MACHINE.md`](STATE_MACHINE.md). Function,
event and error names are the Solidity names in `official/src`.

The two improvements:

- **Bid escrowed at create.** `_beforeSwap` takes the USDC bid as a hook claim (`numeraire.take`).
  `Router._settlePriorityFee` only pays the bid in (`sync`, `safeTransferFrom`, `settleFor(hook)`). There is
  no `recordPriorityFee`.
- **Maker salt (`S.salt`).** The Router appends `order.salt` as the fifth `hookData` word for `T.swap`, and
  `0` for `T.swapWithSig`. A zero salt keeps v2's block-data derivation. The walk `salt = keccak(salt)` steps
  past open ids (`I.SaltFree`).

**Confidence markers** come from the §4 confidence table of `STATE_MACHINE.md` and appear in notes and
edge labels:

| Marker | Meaning |
| --- | --- |
| **[P]** | proved for the model configuration (`N = currency1`, one pool, no fallback, no fee override) |
| **[P1]** | proved only in the v1 model or a separate Lean layer (Book, Admin, Hashing) |
| **[T]** | tested only, in `official/test` |
| **[–]** | not covered |

Abbreviations: **PM** = Uniswap v4 `PoolManager`, **claim** = ERC-6909 balance in the PM, **N** = the
numeraire (USDC, either side of the pool), **bid** = `priorityFee`.

These diagrams replace `v2/docs/order-lifecycle.md`, `contract-call-sequences.md` and the lifecycle part
of `price-key-crossing.md` as the reference for the official protocol. `historical-matching-diagrams.md`
stays historical.

---

## 1. Components and actors

*All value sits in the PoolManager. The hook holds escrow as ERC-6909 claims. FeeVault and NativeClaims are
small unlock-callback contracts, and `FeeVault.collect` is authorized by `hook.owner()`. Edge labels name
the `T.*` transitions. Sources: `official/src/AsyncSwap.sol`, `Router.sol`, `FeeVault.sol`, `NativeClaims.sol`,
`libraries/`. EIP-712 domains are v2's (decision 8).*

```mermaid
flowchart LR
    subgraph Actors
        maker(["Maker"])
        filler(["Filler"])
        keeper(["Keeper / relayer"])
        lp(["LP (environment)"])
        owner(["Hook owner"])
        holder(["Native-claim holder"])
    end

    subgraph Periphery
        router["Router<br/>EIP-712 'AsyncSwap Router','1'<br/>swap · swapWithSig · fillOrder<br/>cancelOrder · cancelWithSig<br/>matchBook · fillFromPoolLiquidity"]
        permit2["Permit2<br/>permitWitnessTransferFrom"]
        vault["FeeVault<br/>collect"]
        nclaims["NativeClaims<br/>redeem"]
    end

    subgraph Hook["AsyncSwap hook · EIP-712 'AsyncSwap','1'"]
        hook["AsyncSwap<br/>beforeInitialize · _beforeSwap · _createOrder<br/>matchNewOrder · executeOrder · cancelOrder<br/>matchBook · tryFillOrderFromPoolLiquidity<br/>updatePrice · updatePriceWithSig<br/>setExecutor · setExecutorWithSig · invalidateNonce<br/>setOrderingMode · sweep · transfer/acceptOwnership"]
        matchLib["AsyncMatching<br/>matchIncoming · matchBook · _crosses<br/>_matchPair · _reduceAfterMatch<br/>fillFromPoolLiquidity · _swapAgainstPool"]
        filLib["AsyncFiller<br/>orders, executors, price levels<br/>fill · cancel · settlePriorityFee"]
        radix["RadixPriceTree<br/>bids · asks · per-level priority tree"]
        sigLib["OrderSignatures<br/>struct hashes, Permit2 witness"]
    end

    pm[("PoolManager<br/>unlock · swap · settle · settleFor · take<br/>mint/burn claims · donate<br/>updateDynamicLPFee")]

    maker -- "T.swap · T.cancelOrder" --> router
    maker -- "T.updatePrice · T.setExecutor · T.invalidateNonce" --> hook
    maker -- "signs the order witness" --> permit2
    keeper -- "T.swapWithSig · T.cancelWithSig · T.matchBook · T.fillFromPoolLiquidity" --> router
    keeper -- "T.updatePriceWithSig · T.setExecutorWithSig" --> hook
    filler -- "T.fillOrder" --> router
    lp -- "modifyLiquidity" --> pm
    owner -- "T.setOrderingMode · T.sweep · T.transferOwnership" --> hook
    owner -- "T.collect" --> vault
    holder -- "T.redeem" --> nclaims

    router -- "unlock, PM.swap with hookData" --> pm
    router -- "permitWitnessTransferFrom" --> permit2
    permit2 -- "input tokens" --> pm
    router -- "matchNewOrder · executeOrder · cancelOrder · matchBook · tryFillOrderFromPoolLiquidity" --> hook
    pm -- "T.initialize: beforeInitialize · beforeSwap" --> hook
    hook --> matchLib
    hook --> sigLib
    matchLib --> filLib
    filLib --> radix
    hook -- "take/settle claims · donate · swap · updateDynamicLPFee" --> pm
    vault -- "burn + take" --> pm
    nclaims -- "burn ETH claim + take ETH" --> pm
```

*`T.initialize` only accepts pools that hold N on either side and use the dynamic-fee flag
(`NumeraireRequired`, `DynamicFeeRequired`). This is [T] for the numeraire check, and the dynamic-fee check
is [–]. ETH can only be `currency0` and is never N.*

---

## 2. T.swap: create, bid escrow, matchNewOrder, pool fallback

*One `PM.unlock`, in the exact order of `official/src`: `_beforeSwap` takes the input claim, then
`_createOrder` stores the order and emits `AsyncOrderCreated` with the final salt, then `numeraire.take`
takes the bid claim, then `HookSwap` is emitted. After that the Router settles the input,
`_settlePriorityFee` pays the bid in for the hook, `matchNewOrder` runs `B.matchLoop`, and a remainder tries
`B.poolFill` inside `try/catch`. Sources: `Router.swap` / `unlockCallback` / `_settlePriorityFee`,
`AsyncSwap._beforeSwap` / `_createOrder` / `matchNewOrder`. Lean: `swapBody`, `createBody`, `priorityFeeBody`,
`matchLoop`.*

```mermaid
sequenceDiagram
    autonumber
    actor M as Maker
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook
    participant B as Book (AsyncFiller + RadixPriceTree)

    M->>R: swap(order, userData)
    Note over R: owner == msg.sender, userData user/executor/min/bid match the order,<br/>native input needs msg.value == amountIn
    R->>PM: unlock(Swap)
    PM->>R: unlockCallback
    R->>PM: swap(key, -amountIn, sqrtPrice, hookData = UserParams + makerSalt)
    Note over R: makerSalt = order.salt for Swap, 0 for SwapWithSig
    PM->>H: beforeSwap(sender = Router) runs _beforeSwap
    Note over H: ExactInputOnly, sender == executor and isExecutor[user][executor],<br/>amountIn > 0 and min > 0 (ZeroAmount)
    H->>PM: take(in, hook, amountIn, claims) - input claim
    H->>H: _createOrder, S.salt: makerSalt if non-zero, else the v2 block-data hash<br/>while orders[id] is open, salt = keccak(salt)
    H->>B: addOrder: S.Free to S.Open, sequence = ++nextSequence, append to its level
    Note over B: FIFO needs bid == 0. PriorityFee needs 100_000 <= bid <= 2^64-1
    H-->>H: tstore pending match id and executor, emit AsyncOrderCreated with the final salt
    H->>PM: numeraire.take(hook, bid, claims) if bid > 0 - bid claim
    H-->>H: emit HookSwap
    H-->>PM: BeforeSwapDelta(+amountIn, 0)
    Note over H,PM: [P] I.Escrow and I.Backing after create (N = currency1).<br/>[–] proof that the one-step bid escrow equals createBody + priorityFeeBody, [T] test_bidEscrowedInCreateUnlock.<br/>I.SaltFree is assumed, [T] salt tests
    PM-->>R: Router owes amountIn
    R->>PM: settle input (transferFrom maker, or msg.value for ETH)
    R->>PM: _settlePriorityFee: sync(N), safeTransferFrom(maker, PM, bid), settleFor(hook)
    Note over R: nothing else. An unpaid bid leaves the hook delta at -bid and the unlock reverts
    R->>H: matchNewOrder(order)
    Note over H: the pending id and executor must match, then are cleared
    loop B.matchLoop, matchIncoming, at most 8 pairs while the order is open
        H->>B: best opposite level, then bestAtPrice
        H->>H: _crosses, then B.matchPair, which runs B.reduceSide on both orders
    end
    Note over H: [P] ledgers of the match loop. [T] that each pair is the book's best (I.Priority link)
    alt order still S.Open
        H->>H: try this.fillOrderFromPoolLiquidity(order, id), which is B.poolFill
        Note over H: [T] pool fallback. A revert is caught, the attempt rolls back,<br/>and earlier matches and the open remainder stay
    end
    Note over PM: I.DeltaZero, every locker delta is 0 [P]
    R-->>M: order id is emitted in AsyncOrderCreated
```

*[T] `I.BalNonNeg` on a buy-side swap with a bid (gap `hgap`). [T] `N = currency0`.*

---

## 3. T.fillOrder, with fee flows

*The filler pays the live gross output from storage: `live = amountOutMin + fee(amountOutMin)`, where
`fee = floor(3·m/997)` is 30 bps of gross. `live` must not exceed `maxPrice`. The filler receives the whole
input through `B.payOut`. The maker gets exactly `m`, the vault gets the fee as a claim, the bid goes to
`B.settleBid`, and the order moves `S.Open` → `S.Closed` (Filled). Sources: `Router.fillOrder` /
`unlockCallback` (FillOrder), `AsyncSwap.executeOrder`, `AsyncFiller.fill`. Lean: `fillBody`, `fillGuard`,
`fill_settlement`. All [P] except where marked.*

```mermaid
sequenceDiagram
    autonumber
    actor F as Filler
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook
    participant V as FeeVault
    actor M as Maker
    actor LP as LPs

    F->>R: fillOrder(order, maxPrice, data), plus msg.value if out is ETH
    opt out is native ETH
        R->>H: asyncOrderInfo gives live, msg.value must equal live
        R->>H: forward live ETH, receive() adds it to PENDING_NATIVE_DEPOSIT
    end
    R->>PM: unlock(FillOrder)
    PM->>R: unlockCallback
    R->>H: asyncOrderInfo gives live = m + fee(m) from storage
    Note over R: "Price exceeds maxPrice" if live > maxPrice
    opt out is ERC-20
        R->>PM: sync(out), safeTransferFrom(filler, PM, live), settleFor(hook)
    end
    R->>H: executeOrder(order, abi.encode(filler))
    opt out is native ETH
        H->>H: pending >= live (UnaccountedNativeOutput), pending -= live
        H->>PM: settle(ETH, live)
    end
    Note over H: AsyncFiller.fill checks isExecutor[owner][Router] and OrderNotFound
    H->>PM: pay(out, maker, m)
    H->>PM: take(out, FeeVault, fee, claims), emit OrderFeeAccrued
    PM-->>V: fee claim
    H->>PM: B.payOut(in, filler, amountIn)
    alt hasLiquidity
        H->>PM: B.settleBid donates the bid
        PM-->>LP: reserves[N] += bid
    else no liquidity
        H->>PM: B.settleBid forfeits the bid, claims[N][vault] += bid
    end
    H-->>H: delete, S.Closed (Filled), emit AsyncOrderFilled
    Note over H,PM: [P] fill_settlement, fillBody_deltasZero, I.Escrow, I.Backing.<br/>[P1] fillOrder_ignores_calldata_amounts, fill_requires_grant.<br/>[T] I.HookHoldsNoTokens at step level
```

---

## 4. T.fillFromPoolLiquidity: B.poolFill with the 0.30% override

*The hook swaps the whole escrow against LP liquidity. The hook is the swap's sender, so it skips its own
`beforeSwap` and no order is created. The dynamic LP fee is set to `3000` (0.30%) for this swap and the
previous fee is restored afterwards. The swap must consume all of the input and return `y ≥ minOut`.
Sources: `Router.fillFromPoolLiquidity` → `AsyncSwap.tryFillOrderFromPoolLiquidity` →
`fillOrderFromPoolLiquidity` → `AsyncMatching.fillFromPoolLiquidity` / `_swapAgainstPool`. Lean:
`liquidityFillBody`, `liquidityFillGuard`. Decision 10.*

```mermaid
sequenceDiagram
    autonumber
    actor K as Keeper
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook
    actor M as Maker
    actor LP as LPs

    K->>R: fillFromPoolLiquidity(order)
    R->>PM: unlock(PoolLiquidityFill)
    PM->>R: unlockCallback
    R->>H: tryFillOrderFromPoolLiquidity(order)
    Note over H: isExecutor[owner][Router] [T], order open
    H->>H: try this.fillOrderFromPoolLiquidity(order, id)
    Note over H: getLiquidity != 0, else NoActiveLiquidity
    H->>PM: burn the hook's input claim, settle amountIn
    H->>PM: previousFee = getSlot0().lpFee
    H->>PM: updateDynamicLPFee(key, 3000)
    H->>PM: swap(exact input amountIn, no price limit, empty hookData)
    PM->>LP: reserves[in] += amountIn, reserves[out] -= y, LPs earn 0.30%
    PM-->>H: delta(-amountIn, +y)
    H->>PM: updateDynamicLPFee(key, previousFee)
    Note over H: [–] fee override and restore are not modelled or asserted
    Note over H: whole input used, else PartialLiquidityFill.<br/>y >= minOut, else LimitPriceNotMet
    H->>PM: pay(out, maker, y)
    H->>PM: B.settleBid(bid)
    H-->>H: delete, S.Closed (PoolFilled), emit AsyncOrderLiquidityFilled
    alt any check reverts
        H-->>R: caught, returns false, the order stays S.Open [T]
    end
    Note over H,PM: [P] I.Escrow, I.Backing, liquidityFillBody_deltasZero with y as an input.<br/>[P1] liquidityFill_meets_min at the book layer
```

*This path charges no protocol fee. The LPs' 0.30% applies instead.*

---

## 5a. T.matchBook by a keeper

*Anyone can clear a crossed book. The loop takes the best bid against the best ask while `_crosses` holds,
up to `maxMatches` (1 to 8, else `InvalidMatchBound`). In `B.matchPair` the older order rests and its price
sizes the trade, and a zero result stops the loop. `B.reduceSide` pays the counterparty, settles the pro-rata
bid, and either closes the order (S.Closed, Matched) or resequences it. There is no pool fallback. Sources:
`AsyncMatching.matchBook` / `_crosses` / `_matchPair` / `_reduceAfterMatch` / `_settleMatchedPriorityFee`.
Lean: `matchLoop`, `matchPairBody`, `reduceSideBody`.*

```mermaid
sequenceDiagram
    autonumber
    actor K as Keeper
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook
    participant B as Book
    actor S as Seller
    actor Bu as Buyer

    K->>R: matchBook(key, maxMatches)
    R->>PM: unlock(MatchBook)
    PM->>R: unlockCallback
    R->>H: matchBook(key, maxMatches)
    loop B.matchLoop until maxMatches, an empty side, or no cross
        H->>B: bids.best(true), asks.best(false), then bestAtPrice on each side
        H->>H: _crosses(bidKey, askKey) [T exact equal-key rule]
        H->>H: B.matchPair: _matchAmounts with restingBuy = buy is older
        alt asset == 0 or quote == 0
            H-->>H: stop
        else trade
            H->>PM: B.reduceSide(sell): B.payOut(asset to Buyer), B.settleBid(floor(bid*used/amountIn))
            H->>PM: B.reduceSide(buy): B.payOut(quote to Seller), B.settleBid(pro-rata share)
            alt remaining input or remaining min is 0
                H->>PM: B.settleBid(rest of bid), B.payOut(unused input to owner)
                H->>B: delete, S.Closed (Matched)
            else partial
                H->>B: store the reduced amounts. If the price key changed, sequence = ++nextSequence
                Note over B: [T] resequencing (decision 7), ledgers [P]
            end
            H-->>H: emit AsyncOrdersMatched
        end
    end
    Note over H,PM: [P] I.Escrow, I.Backing, I.DeltaZero, matchLoop_head_sound, matchBook_frame.<br/>[P1] best pair at the book layer, [T] link to the state machine
```

## 5b. T.cancelOrder, with B.settleBid

*The maker cancels. The Router checks the owner, and the hook accepts the owner or a granted executor. The
input comes back through `B.payOut`, and the bid is never refunded: `B.settleBid` donates it if
`hasLiquidity`, or forfeits it to the vault. Sources: `Router.cancelOrder`, `AsyncSwap.cancelOrder`,
`AsyncFiller.cancel` / `settlePriorityFee`. Lean: `cancelBody`, `settleBidBody`, `cancel_settlement`.*

```mermaid
sequenceDiagram
    autonumber
    actor M as Maker
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook
    participant V as FeeVault
    actor LP as LPs

    M->>R: cancelOrder(order)
    Note over R: "Only owner can cancel"
    R->>PM: unlock(Cancel)
    PM->>R: unlockCallback
    R->>H: cancelOrder(order)
    Note over H: executor == owner or isExecutor[owner][executor], OrderNotFound
    H->>PM: B.payOut(in, maker, amountIn). ETH is paid as a claim
    alt hasLiquidity
        H->>PM: B.settleBid: donate(bid), burn the hook's N claim
        PM-->>LP: reserves[N] += bid
        H-->>H: emit PriorityFeeDonated
    else no liquidity
        H->>PM: B.settleBid: claims[N][hook] -= bid, claims[N][vault] += bid
        PM-->>V: bid claim
        H-->>H: emit PriorityFeeForfeited
    end
    H-->>H: delete, S.Closed (Cancelled), emit AsyncOrderCancelled
    Note over H,PM: [P] cancel_settlement, cancelBody_deltasZero, I.Escrow, I.Backing.<br/>[P1] cancel_requires_owner_and_grant
```

---

## 6. Signed flows: T.swapWithSig and T.cancelWithSig

*`T.swapWithSig`: a relayer submits an order the maker signed. Permit2 pulls the input only if the signature
covers both the transfer and the witness `hashOrder(order)`. The witness does not cover `sqrtPrice` or `salt`
(decision 6), so the Router always passes `makerSalt = 0` and the salt is derived. An optional executor grant
runs `T.setExecutorWithSig` first. Sources: `Router.swapWithSig` / `_settleWithPermit`,
`AsyncSwap.setExecutorWithSig` / `_verify`. Proof status: [P1] (`swapWithSigBody_deltasZero`, `hashOrder_inj`,
`routerPermit_inj`, `tokens_inj`), plus [T] tests.*

```mermaid
sequenceDiagram
    autonumber
    actor M as Maker
    actor Rl as Relayer
    participant R as Router
    participant H as AsyncSwap hook
    participant PM as PoolManager
    participant P2 as Permit2

    M-->>Rl: off-chain: order, Permit2 signature over the hashOrder witness, optional SetExecutor signature
    Rl->>R: swapWithSig(order, permit, grant)
    Note over R: ERC-20 input only, "Native input needs swap()"
    opt grant signature present and Router is not an executor yet
        R->>H: setExecutorWithSig(key, maker, Router, true, nonce, deadline, sig)
        Note over H: _verify: deadline, burn an unused nonce, SignatureChecker [P1 I.NoReplay]
    end
    R->>PM: unlock(SwapWithSig)
    PM->>R: unlockCallback
    R->>PM: swap(..., hookData = UserParams + 0)
    Note over PM,H: _beforeSwap as in diagram 2, with S.salt always derived
    R->>PM: sync(in)
    R->>P2: permitWitnessTransferFrom(to = PM, owner = maker, witness = hashOrder(order))
    P2->>PM: amountIn from the maker
    R->>PM: settle()
    R->>PM: _settlePriorityFee: sync(N), safeTransferFrom(maker, PM, bid), settleFor(hook)
    R->>H: matchNewOrder(order), then the pool fallback
```

*`T.cancelWithSig` is [P] in V2, with [P1] `cancelWithSig_no_replay` and [P1] `hashCancel_inj`.*

```mermaid
sequenceDiagram
    autonumber
    actor M as Maker
    actor Rl as Relayer
    participant R as Router
    participant PM as PoolManager
    participant H as AsyncSwap hook

    M-->>Rl: off-chain: CancelOrder(owner, tokenIn, tokenOut, amountIn, orderId, nonce, deadline)
    Rl->>R: cancelWithSig(order, nonce, deadline, sig)
    Note over R: now <= deadline (SignatureExpired), the nonce is burnt before the signature check,<br/>signature valid in 'AsyncSwap Router','1' over the stored amountIn (InvalidSignature)
    R->>PM: unlock(Cancel)
    PM->>R: unlockCallback
    R->>H: cancelOrder(order), as in diagram 5b
```

*`T.updatePriceWithSig` uses the same `_verify` in the `'AsyncSwap','1'` domain and needs no unlock [P1].*

---

## 7. Per-order states: S.Free, S.Open, S.Closed

*This is the per-order state machine of `STATE_MACHINE.md` §2.1. `S.Closed` uses the same storage as `S.Free`;
its label only records how the order closed. A closed slot is free again, and the salt walk only steps past
open ids (`I.SaltFree`). Guards come from §2.4.*

```mermaid
stateDiagram-v2
    state "S.Free" as Free
    state "S.Open" as Open
    state "S.Closed" as Closed {
        state "Matched" as Matched
        state "Filled" as Filled
        state "PoolFilled" as PoolFilled
        state "Cancelled" as Cancelled
    }

    [*] --> Free
    Free --> Open : T.swap / T.swapWithSig [executor granted, amountIn > 0, min > 0, bid rule, I.SaltFree]
    Open --> Open : B.reduceSide partial [both remainders > 0] new sequence if the key changed
    Open --> Open : T.updatePrice / T.updatePriceWithSig [owner, newMin > 0] new sequence
    Open --> Matched : B.matchLoop in T.swap or T.matchBook [remaining input or min reaches 0]
    Open --> Filled : T.fillOrder [Router is executor, live <= maxPrice, output paid]
    Open --> PoolFilled : B.poolFill in T.swap or T.fillFromPoolLiquidity [hasLiquidity, full input, y >= minOut]
    Open --> Cancelled : T.cancelOrder / T.cancelWithSig [owner or executor, or a valid signature]
    Closed --> Free : storage cleared
```

*Every exit from `S.Open` burns exactly the order's remaining escrow: [P] `escrow_closeBody` and
`escrow_reduceSideBody`. A failed `B.poolFill` is caught and the order stays in `S.Open` [T]. A
`B.matchPair` that rounds to zero changes nothing. `T.setOrderingMode` needs an empty book.*

---

## 8. Matching priority: I.Priority and the cross test

*This flowchart shows how `B.matchLoop` picks each pair. Price comes first: the best bid is the highest key
and the best ask the lowest. Within a price level, the ordering mode decides. Crossing uses v2's `_crosses`.
Sources: `AsyncFiller.bestAtPrice` / `_priorityKey`, `AsyncMatching._crosses` / `_reduceAfterMatch`.
`I.Priority` is [P1] at the book layer (`best_spec`, `bestAtPrice_priority`, `priorityKey_lt_iff`,
`fifo_head_earliest`, `reprice_sequence_last`); the link to `matchLoop` is [T].*

```mermaid
flowchart TD
    start(["B.matchLoop: next pair"]) --> empty{"Opposite price tree empty?"}
    empty -- yes --> none(["Stop"])
    empty -- no --> best["Best level<br/>bids: highest key, asks: lowest key<br/>RadixPriceTree.best · I.RadixRefines P1"]
    best --> mode{"Ordering mode"}
    mode -- FIFO --> head["Level queue head<br/>lowest sequence"]
    mode -- PriorityFee --> pk["Highest _priorityKey<br/>= bid shifted left 64, OR maxUint64 - sequence<br/>higher bid, then lower sequence"]
    head --> crossed
    pk --> crossed
    crossed{"_crosses(buyKey, sellKey)"} -- "keys differ" --> cmp{"buyKey > sellKey?"}
    crossed -- "keys equal, T" --> exact{"mulDiv(buyIn, sellIn, sellMin) >= buyMin?"}
    cmp -- no --> none
    exact -- no --> none
    cmp -- yes --> trade["B.matchPair: the older order rests and sizes the trade<br/>I.MakerLimit P: matchAmounts_sound"]
    exact -- yes --> trade
    trade --> zero{"asset or quote == 0?"}
    zero -- yes --> none
    zero -- no --> reduce["B.reduceSide on both orders"]
    reduce --> closed{"Remaining input or min == 0?"}
    closed -- yes --> del["S.Closed (Matched): B.settleBid the rest, B.payOut unused input"]
    closed -- no --> keyChanged{"Price key changed?"}
    keyChanged -- "yes, T decision 7" --> reseq["sequence = ++nextSequence<br/>back of the new level"]
    keyChanged -- no --> feeChanged{"PriorityFee mode and bid dropped?"}
    feeChanged -- yes --> reidx["Re-index _priorityKey, same sequence"]
    feeChanged -- no --> stay["Stay in place"]
    reidx --> start
    stay --> start
    reseq --> start
    del --> start

    reprice(["T.updatePrice / T.updatePriceWithSig"]) -- "P1 reprice_sequence_last" --> reseq
```

*The loop stops after `maxMatches` pairs: at most 8 in `matchNewOrder`, and the given bound in `T.matchBook`.*

---

## 9. Money flow per currency and the invariants

*This diagram shows where each currency `c` moves, and which invariant boxes each flow stays inside. The
status of each invariant matches `STATE_MACHINE.md` §3 and §4.*

```mermaid
flowchart LR
    maker(["Maker wallet"])
    filler(["Filler wallet"])
    cp(["Matched counterparty"])
    lps(["LP positions (environment)"])

    subgraph PM["bal[c][pm] · I.Backing: = supply[c] + reserves[c]"]
        subgraph Escrow["claims[c][hook] · I.Escrow: = open input + open bids"]
            inEsc["Input escrow<br/>any c"]
            bidEsc["Bid escrow<br/>N only · I.BidEscrowed"]
        end
        vaultC["claims[c][vault]<br/>protocol fee, forfeited bids"]
        userC["claims[ETH][user]<br/>native proceeds and refunds"]
        res["reserves[c]"]
    end

    owner(["Hook owner's recipient"])
    eth(["ETH recipient"])

    maker -- "T.swap: take input claim" --> inEsc
    maker -- "T.swap: numeraire.take bid, settleFor(hook)" --> bidEsc

    inEsc -- "T.fillOrder: B.payOut whole input" --> filler
    filler -- "T.fillOrder: live = m + fee" --> PM
    PM -- "T.fillOrder: m" --> maker
    PM -- "T.fillOrder: fee, OrderFeeAccrued" --> vaultC

    inEsc -- "B.reduceSide: used input" --> cp
    inEsc -- "B.reduceSide close, T.cancelOrder: unused input" --> maker

    inEsc -- "B.poolFill: whole input, 0.30% LP fee" --> res
    res -- "B.poolFill: y >= minOut" --> maker

    bidEsc -- "B.settleBid with liquidity: donate" --> res
    bidEsc -- "B.settleBid without liquidity: forfeit" --> vaultC

    vaultC -- "T.collect" --> owner
    userC -- "T.redeem" --> eth
    lps <-- "modifyLiquidity" --> res
```

| Invariant | Statement (per currency `c`) | Status |
| --- | --- | --- |
| `I.Escrow` | `claims[c][hook] = Σ open input in c + Σ open bids if c = N` | **[P]** `step_escrow` over all 10 V2 actions; **[T]** for the pool fallback in create and `N = currency0` |
| `I.HookClaimsNonNeg` | `0 ≤ claims[c][hook]` | **[P]** `step_hook_claims_nonneg` (from `I.Escrow`) |
| `I.Backing` | `bal[c][pm] = supply[c] + reserves[c]` | **[P]** `step_backing`, assuming the PM never acts as a party (`Users`); across LP actions it relies on v4's own accounting (assumed) |
| `I.DeltaZero` | every locker delta is `0` when `unlock` returns | **[P]** `*Body_deltasZero`, `matchLoop_neutral` |
| `I.Conservation` | `Σ_{a∈S} bal[c][a]` unchanged | **[P]** `step_conservation`; **[–]** for `T.swapWithSig`, `T.collect`, `T.sweep` |
| `I.ClaimsNonNeg` | `0 ≤ claims[c][a]` for all `a` | **[P]** `step_claims_nonneg`, needs `I.Escrow` before the step |
| `I.BalNonNeg` | `0 ≤ bal[c][a]` for `a ≠ pm` | **[P]** `step_bal_nonneg` **except** gap `hgap`: a buy-side `T.swap` (`in = N`) with a bid. `swapGuard` checks `amountIn` and `priorityFee` against the maker's N balance separately, not their sum. Solidity reverts on the second `safeTransferFrom`, so this case is **[T]** only. |
| `I.SupplyConsistent` | `supply[c] = Σ_a claims[c][a]` | **[–]** not covered (docstring only) |
| `I.SupplyNonNeg`, `I.ReservesNonNeg`, `I.PmBalNonNeg` | `0 ≤ supply[c]`, `0 ≤ reserves[c]`, `0 ≤ bal[c][pm]` | **[–]** not covered. They would follow from `I.SupplyConsistent` + `I.ClaimsNonNeg`, `liquidityFillGuard`'s `y ≤ reserves[out]`, and `I.Backing` (§4 item 10) |
| `I.BidEscrowed` | every open order's bid is held in `claims[N][hook]` | **[P]** at create only (`created_order_escrowed`); the global form `step_all_escrowed` is **[–]**; **[T]** `test_bidEscrowedInCreateUnlock` |
| `I.HookHoldsNoTokens` | `bal[c][hook]` unchanged by fill and cancel | **[P]** as a conjunct of `fill_settlement` / `cancel_settlement`; the step-level form is **[T]**. A native fill passes ETH through the hook transiently via `PENDING_NATIVE_DEPOSIT`. |

*How to read the diagram: every arrow leaving the `I.Escrow` box is a `B.payOut`, `B.settleBid` or
`B.poolFill` burn, the same size as the payment, in the same unlock. That is why each entry point keeps
`I.Escrow` (`escrow_reduceSideBody`, `escrow_matchLoop`, `escrow_closeBody`) and nets the hook's deltas to
zero (`payOutBody_neutral`, `settleBidBody_neutral`). Native ETH paid to a user lands in
`claims[ETH][user]` and leaves only through `T.redeem`. `T.sweep` moves only `bal[c][hook]` and never
touches claims ([P1] `sweep_settlement`).*
