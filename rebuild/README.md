# asyncswap v2, rebuilt from the proofs

A from-scratch Solidity implementation of the Async Swap v2 protocol, written only from the Lean 4
specification in this repository (first draft from `dev` @ `1969fd0`). The original `asyncswap/v2` sources
were not consulted, and the rebuilder that maintains this folder never reads them: the editor compares the
two and files what differs. The algorithm is in [`.github/formalmind/cycle.md`](../.github/formalmind/cycle.md).

```sh
forge build --sizes --root rebuild
forge test --root rebuild                               # 97 tests: unit, fuzz, invariant
FOUNDRY_INVARIANT_RUNS=256 FOUNDRY_INVARIANT_DEPTH=96 forge test --root rebuild --match-contract Invariant
```

## Contracts

| Contract | What it does | Lean source |
| --- | --- | --- |
| `AsyncSwap` | v4 hook: `beforeInitialize` admits only dynamic-fee pools containing the numeraire; `beforeSwap` turns an exact-input swap into an escrowed limit order; match, fill, cancel, reprice, liquidity fill, signed actions, admin | `AsyncSwapProtocol/V2/Model.lean`, `AsyncSwapSpec/Book.lean`, `Admin.lean` |
| `Router` | user entry points and the unlock callback; `swap`, `swapWithSig` (Permit2 witness), `fillOrder`, `cancelOrder`, `cancelWithSig`, `matchBook`, `fillFromPoolLiquidity` | `V2/Model.lean`, `AsyncSwapProtocol/Model.lean`, `Hashing.lean` |
| `FeeVault` | holds fees and forfeited bids as ERC-6909 claims; owner `collect` | `Model.lean` `collectFees` |
| `NativeClaims` | redeems native-ETH claims for ETH | `V2/Model.lean` `redeemNative` |
| `RadixPriceTree` | Patricia trie over `uint128` keys, storage layout and id recycling as specified | `RadixTree.lean`, `RadixStorage/Insert/Remove.lean`, `Bounds.lean` |
| `AsyncFiller` | order storage, price levels, FIFO / priority-bid ordering, partial-fill reduction | `Order.lean`, `Priority.lean`, `Reduce.lean`, `Book.lean` |
| `AsyncMatching` | `_matchAmounts`, line for line | `Match.lean` |
| `ProtocolFee` | 30 bps of gross, split form | `Fee.lean` |
| `OrderSignatures` | EIP-712 type strings and struct hashes, Permit2 witness | `Hashing.lean` |

## Theorems checked as tests

| Test | Theorem(s) |
| --- | --- |
| `RadixPriceTree.t.sol` | `best_true_spec` / `best_false_spec` vs a linear scan, `insert_wf` / `remove_wf` (Patricia invariant walked in storage), set semantics, `remove_absent`, `solMsb_eq_log2`, `IdAlloc.run_next_le_peak` |
| `AsyncMatching.t.sol` | `matchAmounts_sound`, `matchAmounts_cross`, `*_tight` |
| `ProtocolFee.t.sol` | `poolFee_eq`, `poolFee_eq_30bps_of_gross`, `poolFee_le_net`, `poolFee_mono`, `poolFee_eq_zero_iff` |
| `OrderSignatures.t.sol` | type strings, `hashOrder_inj` (salt / sqrtPrice not covered), `orderId_inj`, type separation |
| `Lifecycle.t.sol` | `fill_settlement`, `fill_fee_is_30bps`, `fillOrder_ignores_calldata_amounts`, `fill_closes`, `cancel_settlement`, `redeem_settlement`, `collect_settlement`, `sweep_settlement`, `owner_change_only_via_accept`, `created_order_escrowed`, mode / bid bounds |
| `Matching.t.sol` | `maker_limit_honored`, `runLegs_priorityFee`, `bestAtPrice_priority`, `fifo_head_earliest`, `reprice_sequence_last`, `best_bid_is_max`, `liquidityFill_meets_min`, `MAX_MATCHES_PER_CALL` |
| `Signatures.t.sol` | `verify_no_replay`, `verify_respects_deadline`, `hashUpdatePrice_inj`, `cancelWithSig_no_replay`, `digest_ne_of_contract`, `routerPermit_inj` |
| `Invariants.t.sol` | `Escrow` (hook claims = open input + bids, per currency), `Escrow.wf`, `PriceIndex.best_spec` with priority ranking, hook holds no tokens, claims backed (FIFO and PriorityFee pools, with the numeraire as currency1 and as currency0) |
| `Numeraire.t.sol` | beyond the model: pool admission, sides, price keys, matching, fills and bids with the numeraire as currency0 |

Tests are evidence, not proofs. The Lean theorems are about the Lean model; nothing here proves that this
Solidity refines that model.

## Beyond the model: the numeraire on either side

The Lean model fixes the numeraire (USDC) as `currency1`, so there a buy is `!zeroForOne` and bids are
`currency1` claims. On a real chain USDC can sort as either currency: on mainnet USDC/WETH it is `currency0`.
This implementation generalises the model:

- the hook takes the numeraire as a constructor argument (a token, never native) and `beforeInitialize`
  rejects any pool that does not contain it;
- each order records its side at creation, `buy = (input == numeraire)`, and price keys, best bid / ask and
  matching use that;
- bids are pulled, escrowed, donated and forfeited in the numeraire, on whichever side of the pool it sits.

ETH can be the traded asset (ETH/USDC: native is always `currency0`), never the numeraire.

Pools must also use the dynamic-fee flag, so a pair cannot be split into one book per static fee tier. A
dynamic-fee pool starts with a zero LP fee; the only swaps that reach the pool's liquidity are the hook's own
`fillFromPoolLiquidity` swaps, and the hook sets the LP fee to 0.30% before each one.

With the numeraire as `currency1` this is exactly the model. The `currency0` case has no Lean counterpart; it
is checked by `Numeraire.t.sol` and by the invariant suites run on `flipKey` / `flipPrioKey`.

## What the proofs did not determine

These are my choices. The real v2 contracts may differ on any of them.

- **Price-level structure.** The spec abstracts a level as a queue plus, in priority mode, a priority-key
  trie. Here a level is a doubly linked list kept in sequence order, plus that trie.
- **Partial fills keep time priority.** A reduced order keeps its sequence. It moves level only if its
  price key changes (or, in priority mode, its remaining bid changes). The spec only says a *reprice*
  re-enters last.
- **Bid escrow in one step.** The model has a separate `recordPriorityFee` and an `escrowed` flag. Here
  `beforeSwap` mints the bid claim and the Router settles it for the hook in the same unlock, so every stored
  bid is escrowed and the flag is gone.
- **Salt walk.** The spec only says "the chosen slot is free". Here it is `salt = keccak256(salt)` until free.
- **Interfaces.** Function signatures, `UserParams` (it carries the salt), errors, events, the
  `lastOrderId` transient read-back, and the EIP-712 domain names / versions (`AsyncSwap` / `AsyncSwapRouter`,
  `"2"`).
- **Out of model.** Gas, events and revert reasons are not modelled. Uniswap pool math is taken from v4-core.
  Permit2 is a mock that implements the real `hashWithWitness` digest.

## Build notes

`via_ir = true` with `optimizer_runs = 200`: v4-core's PoolManager needs via-IR, 1000 runs hits a Yul stack
error in `Pool.swap`, and 10000+ runs takes the hook over EIP-170. The hook is ~21.5 KB.
