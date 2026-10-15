# asyncswap/v2-proofs

Lean 4 + Mathlib specification and machine-checked proofs for the Async Swap protocol.

| Library | Scope | Reference source |
| --- | --- | --- |
| `AsyncSwapSpec` | v2 hook: protocol fee, order matching, partial fills, escrow invariant, admin, `RadixPriceTree` | `asyncswap/v2` `src/` |
| `AsyncSwapProtocol` | Call-sequence state machine from the README sequence diagram: Router → PoolManager → hook → FeeVault, token ledgers, claims, deltas | `AsyncSwap Production/packages/protocol/src` @ `fcf75d4` |

`lake build` checks every theorem. No `sorry`, no extra axioms. See [README.spec.md](README.spec.md)
for the theorem-by-theorem map of `AsyncSwapSpec`, and the module docstrings in
`AsyncSwapProtocol/` for the protocol model.

```sh
lake exe cache get   # Mathlib build cache
lake build
```

CI runs `lake build` on every push and pull request (`.github/workflows/lean.yml`).
Pushes to the protocol repositories trigger the formal-mind bot (`.github/workflows/formal-mind.yml`),
which updates the spec for the new commit and opens a pull request here.
