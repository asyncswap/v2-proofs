import AsyncSwapSpec.Fee
import AsyncSwapSpec.Match
import AsyncSwapSpec.Reduce
import AsyncSwapSpec.Priority

/-!
# Overflow and counter bounds (decision 2)

Amounts are unbounded in the model; here are the explicit input bounds under which every
arithmetic site in the v2 contracts stays inside its machine width (so Solidity's checked
arithmetic and `Math.mulDiv`'s overflow revert can never fire), and the two monotone counters
whose exhaustion would stop the book.

| Site | Bound |
| --- | --- |
| `calculatePoolFee(net)` | never overflows for any `uint256` (`poolFee_le_net`) |
| `amountOutMin + fee` (`livePrice`, `executeOrder`) | `net ≤ (2^256 − 1) · 997 / 1000` ⇒ `gross < 2^256` |
| `_priceKey` `mulDiv(amount, 1e18, other)` | `amount · 10^18 < 2^256` (≈ `amount < 1.16e58`) ⇒ no revert |
| `_matchAmounts` `mulDiv(sell.in, buy.in, buy.min)` etc. | both inputs `< 2^128` ⇒ every intermediate `< 2^256` |
| `_settleMatchedPriorityFee` `mulDiv(fee, used, old)` | always `≤ fee < 2^64` |
| `uint64 sequence` | the `n`-th order or reprice gets sequence `n`; fits while `n ≤ 2^64 − 1` |
| `uint32` radix node ids | never reused; the `n`-th distinct price level needs id `2n − 1`; `insert` reverts (`NodeIdOverflow`) once `2n − 1 > 2^32 − 1`, i.e. from the 2^31-th level on |
-/

namespace AsyncSwap

def uint256Max : ℕ := 2 ^ 256 - 1

/-! ## Fee -/

/-- `calculatePoolFee` cannot overflow: it is at most its input. -/
theorem poolFee_lt_two_pow_256 {net : ℕ} (h : net < 2 ^ 256) : poolFee net < 2 ^ 256 :=
  lt_of_le_of_lt (poolFee_le_net net) h

/-- `net + fee` fits whenever `net` is at most 99.7 % of the range. -/
theorem gross_lt_two_pow_256 {net : ℕ} (h : net ≤ uint256Max * 997 / 1000) : gross net < 2 ^ 256 := by
  unfold gross uint256Max at *
  rw [poolFee_eq]
  omega

/-! ## Price keys -/

/-- `_priceKey` never reverts in `mulDiv` when the scaled amount fits. -/
theorem priceKey_mulDiv_lt {a b : ℕ} (ha : a * priceScale < 2 ^ 256) (hb : 0 < b) :
    mulDiv a priceScale b < 2 ^ 256 := by
  unfold mulDiv
  exact lt_of_le_of_lt (Nat.div_le_self _ _) ha

theorem priceKey_mulDiv_lt_of_small {a b : ℕ} (ha : a < 2 ^ 196) (hb : 0 < b) :
    mulDiv a priceScale b < 2 ^ 256 := by
  apply priceKey_mulDiv_lt _ hb
  unfold priceScale
  calc a * 10 ^ 18 < 2 ^ 196 * 10 ^ 18 := Nat.mul_lt_mul_of_pos_right ha (by norm_num)
    _ < 2 ^ 256 := by norm_num

/-! ## Matching -/

/-- Every `mulDiv` in `_matchAmounts` stays below `2^256` when both inputs are `uint128`
    (open orders have positive input, see `Escrow.wf`). -/
theorem matchAmounts_intermediates_lt (sell buy : Order)
    (hs : sell.amountIn < 2 ^ 128) (hb : buy.amountIn < 2 ^ 128)
    (hs0 : 0 < sell.amountIn) (hb0 : 0 < buy.amountIn) :
    mulDiv sell.amountIn buy.amountIn buy.amountOutMin < 2 ^ 256
    ∧ mulDiv buy.amountIn sell.amountIn sell.amountOutMin < 2 ^ 256
    ∧ (∀ q ≤ buy.amountIn, mulDivCeil q buy.amountOutMin buy.amountIn ≤ buy.amountOutMin)
    ∧ (∀ a ≤ sell.amountIn, mulDivCeil a sell.amountOutMin sell.amountIn ≤ sell.amountOutMin) := by
  have hprod : sell.amountIn * buy.amountIn < 2 ^ 256 := by
    calc sell.amountIn * buy.amountIn < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' hs hb
      _ = 2 ^ 256 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mulDiv; exact lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  · unfold mulDiv; rw [Nat.mul_comm]; exact lt_of_le_of_lt (Nat.div_le_self _ _) hprod
  · intro q hq
    have := mulDivCeil_mul_lt (a := q) (b := buy.amountOutMin) hb0
    have h2 : mulDivCeil q buy.amountOutMin buy.amountIn * buy.amountIn < (buy.amountOutMin + 1) * buy.amountIn := by
      calc _ < q * buy.amountOutMin + buy.amountIn := this
        _ ≤ buy.amountIn * buy.amountOutMin + buy.amountIn := by
          apply Nat.add_le_add_right; exact Nat.mul_le_mul_right _ hq
        _ = (buy.amountOutMin + 1) * buy.amountIn := by ring
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h2)
  · intro a ha
    have := mulDivCeil_mul_lt (a := a) (b := sell.amountOutMin) hs0
    have h2 : mulDivCeil a sell.amountOutMin sell.amountIn * sell.amountIn < (sell.amountOutMin + 1) * sell.amountIn := by
      calc _ < a * sell.amountOutMin + sell.amountIn := this
        _ ≤ sell.amountIn * sell.amountOutMin + sell.amountIn := by
          apply Nat.add_le_add_right; exact Nat.mul_le_mul_right _ ha
        _ = (sell.amountOutMin + 1) * sell.amountIn := by ring
    exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h2)

/-- The pro-rata bid share always fits `uint64`. -/
theorem donatedFee_lt_two_pow_64 (o : Order) (l : Leg) (hfee : o.priorityFee < 2 ^ 64)
    (hused : l.used ≤ o.amountIn) : o.donatedFee l < 2 ^ 64 :=
  lt_of_le_of_lt (mulDiv_le_of_le hused) hfee

/-! ## Monotone counters -/

/-- `++nextSequence`: after `n` creates or reprices the counter is `n`. -/
def sequenceAfter (n : ℕ) : ℕ := n

theorem sequence_fits_uint64 {n : ℕ} (h : n ≤ maxUint64) : sequenceAfter n ≤ maxUint64 := h

/-- `RadixPriceTree._newNode` ids are allocated by `++nextNodeId` and never reused by
    `remove`; the first distinct price costs one id (a leaf), every later one two (leaf +
    branch).  After `n ≥ 1` distinct levels have been inserted into one tree, `nextNodeId = 2n − 1`. -/
def nodeIdsAfter (n : ℕ) : ℕ := if n = 0 then 0 else 2 * n - 1

theorem nodeIdsAfter_succ (n : ℕ) (hn : 0 < n) : nodeIdsAfter (n + 1) = nodeIdsAfter n + 2 := by
  unfold nodeIdsAfter; split_ifs <;> omega

/-- **Longevity bound.** `_newNode` reverts with `NodeIdOverflow` when the incremented id wraps
    to `0`, i.e. when `nextNodeId = 2^32 − 1` before the allocation.  Inserting the `(n+1)`-th
    distinct level needs two ids, so it succeeds iff `2n + 1 ≤ 2^32 − 1`: a single pool-side
    tree can admit at most `2^31 − 1` further distinct price levels after the first.  (Ids are
    per tree: bids, asks and each priority level have their own counter.) -/
theorem insert_level_fits {n : ℕ} (hn : 0 < n) : nodeIdsAfter (n + 1) ≤ 2 ^ 32 - 1 ↔ n ≤ 2 ^ 31 - 1 := by
  unfold nodeIdsAfter
  rw [if_neg (Nat.succ_ne_zero n)]
  norm_num
  omega

end AsyncSwap
