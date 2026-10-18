# asyncswap/v2-proofs

Lean 4 + Mathlib specification and machine-checked proofs for the Async Swap protocol.

| Library | Scope | Reference source |
| --- | --- | --- |
| `AsyncSwapSpec` | v2 hook: protocol fee, order matching, partial fills, escrow invariant, admin, `RadixPriceTree` | `asyncswap/v2` `src/` |
| `AsyncSwapProtocol` | Call-sequence state machine from the README sequence diagram: Router → PoolManager → hook → FeeVault, token ledgers, claims, deltas. `AsyncSwapProtocol/V2/` extends it to v2 (priority bids, matching, liquidity fills, NativeClaims) with lifecycle, settlement, delta neutrality, backing, escrow and conservation theorems | v1: `AsyncSwap Production/packages/protocol/src` @ `fcf75d4`; v2: `asyncswap/v2` `src/` |

`lake build` checks every theorem. No `sorry`, no extra axioms. See [README.spec.md](README.spec.md)
for the theorem-by-theorem map of `AsyncSwapSpec`, and the module docstrings in
`AsyncSwapProtocol/` for the protocol model.

```sh
lake exe cache get   # Mathlib build cache
lake build
```

`FORMAL_MIND.md` is the changelog of every bot run (and of human changes that touch theorems).
CI runs `lake build` only on pushes to `main` (`.github/workflows/lean.yml`); pull requests are reviewed, not built.
Pushes to the protocol repositories trigger the formal-mind bot (`.github/workflows/formal-mind.yml`),
which updates the spec for the new commit and opens a pull request here.

## Plan

Decisions, standing assumptions, findings and the roadmap moved to [.formal/plan.md](.formal/plan.md).
The swarm's config is in [.formal/notebook.json](.formal/notebook.json).
