import Mathlib.Tactic

/-!
# Protocol fee

Models `AsyncSwap.calculatePoolFee` (src/AsyncSwap.sol):

```solidity
function calculatePoolFee(uint24, uint256 amount) public pure virtual returns (uint256) {
    // net * 3 / 997 is equivalent to 30 bps of gross (net + fee), rounded down.
    // Split the calculation to avoid overflowing for large uint256 amounts.
    return (amount / 997) * 3 + ((amount % 997) * 3) / 997;
}
```

`amount` is the maker's *net* minimum output. The filler pays `net + fee` (gross);
the vault receives `fee`. We prove the comment above is literally true.
-/

namespace AsyncSwapProtocol

/-- `calculatePoolFee(net)` exactly as written in Solidity (split form). -/
def poolFee (net : ℕ) : ℕ := (net / 997) * 3 + ((net % 997) * 3) / 997

/-- Gross output the filler must deliver: maker's net minimum plus the fee. -/
def gross (net : ℕ) : ℕ := net + poolFee net

/-- The split form equals the straightforward `net * 3 / 997`.  This is the
    overflow-avoidance rewrite the Solidity comment claims. -/
theorem poolFee_eq (net : ℕ) : poolFee net = net * 3 / 997 := by
  unfold poolFee; omega

/-- The fee is exactly 30 bps of *gross*, rounded down: `fee = ⌊3 · gross / 1000⌋`. -/
theorem poolFee_eq_30bps_of_gross (net : ℕ) : poolFee net = 3 * gross net / 1000 := by
  unfold gross; rw [poolFee_eq]; omega

/-- Upper bound: `1000 · fee ≤ 3 · gross`. -/
theorem poolFee_le_30bps (net : ℕ) : poolFee net * 1000 ≤ 3 * gross net := by
  unfold gross; rw [poolFee_eq]; omega

/-- Lower bound: the rounding loss is less than one unit of output. -/
theorem poolFee_rounding_loss (net : ℕ) : 3 * gross net < poolFee net * 1000 + 1000 := by
  unfold gross; rw [poolFee_eq]; omega

/-- The fee never exceeds the maker's net output (so `net + fee` fits whenever `2·net` does). -/
theorem poolFee_le_net (net : ℕ) : poolFee net ≤ net := by
  rw [poolFee_eq]; omega

/-- Fee is monotone in the net amount: repricing an order upward never lowers the fee. -/
theorem poolFee_mono {a b : ℕ} (h : a ≤ b) : poolFee a ≤ poolFee b := by
  rw [poolFee_eq, poolFee_eq]; omega

@[simp] theorem poolFee_zero : poolFee 0 = 0 := by rfl

/-- Dust orders (net < 333) pay no fee. -/
theorem poolFee_eq_zero_iff (net : ℕ) : poolFee net = 0 ↔ net < 333 := by
  rw [poolFee_eq]; omega

/-- Filler's gross payment is split exactly between maker and vault: nothing is lost
    in the hook (`_fill`: `output.take(owner, amountOutMin)` then `output.take(feeVault, fee)`
    out of a settled `amountOutMin + fee`). -/
theorem gross_split (net : ℕ) : gross net = net + poolFee net := rfl

end AsyncSwapProtocol
