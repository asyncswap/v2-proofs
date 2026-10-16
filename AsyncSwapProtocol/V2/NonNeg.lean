import AsyncSwapProtocol.V2.Invariants

/-!
# Non-negativity of the hook's claim balances (v2)

Roadmap item 2 proved conservation and the escrow equation but left the sign of balances open.
This module closes the first part: what one open order obliges the hook to hold (`escrowOf`) is
a sum of natural-number order fields, so the total `owed` is non-negative, and under `Escrow`
(hook claims = open input + escrowed bids) so is the hook's ERC-6909 claim balance in every
currency, before and after every v2 entry point.

Still open: user (maker / filler) claim balances, PoolManager-side totals (`Backing`), and the
native-ETH ledger entries, which are signed deltas by construction.
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-- One open order never obliges the hook to hold a negative amount. -/
theorem escrowOf_nonneg (c : Currency) (k : OrderKey) (i : OrderInfo) : 0 ≤ escrowOf c k i := by
  unfold escrowOf
  split_ifs <;> omega

/-- The hook's total obligation per currency is a sum of non-negative terms. -/
theorem owed_nonneg (c : Currency) (w : World) : 0 ≤ owed c w :=
  Finset.sum_nonneg (fun k _ => escrowOf_nonneg c k (w.orders k))

/-- **Under `Escrow`, the hook's claim balance is non-negative in every currency.** -/
theorem Escrow.hook_claims_nonneg {cfg : Config} {w : World} (h : Escrow cfg w) (c : Currency) :
    0 ≤ w.claims c cfg.hook := by
  rw [h.claims c]; exact owed_nonneg c w

/-- **After any v2 entry point the hook's claim balance stays non-negative**, under the same
    environment assumptions as `step_escrow`. -/
theorem step_hook_claims_nonneg {cfg : Config} {w w' : World} {a : Action} (hE : Escrow cfg w)
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.hook ∧ o.owner ≠ cfg.pm)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.hook)
    (hredeem : ∀ s n r, a = .redeemNative s n r → s ≠ cfg.hook) (c : Currency) :
    0 ≤ w'.claims c cfg.hook :=
  (step_escrow hE h hswap hfill hredeem).hook_claims_nonneg c

end AsyncSwapProtocol.V2
