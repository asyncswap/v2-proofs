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
| `uint32` radix node ids | recycled by `remove` (fix for the exhaustion finding); the counter tracks the peak number of simultaneous levels, so `insert` cannot overflow while fewer than `2^31` prices are stored at once |
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

/-! ### Radix node ids with recycling (fix for the exhaustion finding)

`RadixPriceTree._newNode` pops a released id from `freeIds` before growing `nextNodeId`, and
`remove` releases the ids of the deleted leaf and branch.  Modelled as a counter machine: a
`Tree` holds `levels` live prices, `next` is the high-water mark of ids ever handed out and
`free` the number of released ids.  Live ids are `2·levels − 1` (one leaf per price, one
branch per price beyond the first). -/

structure IdAlloc where
  levels : ℕ
  next : ℕ
  free : ℕ
  deriving Repr, DecidableEq

/-- Ids in use for `levels` live prices. -/
def liveIds (levels : ℕ) : ℕ := if levels = 0 then 0 else 2 * levels - 1

/-- `insert` of a new price: needs `liveIds (levels+1) − liveIds levels` fresh ids, each taken
    from the free list first. -/
def IdAlloc.insert (a : IdAlloc) : IdAlloc :=
  let need := liveIds (a.levels + 1) - liveIds a.levels
  let fromFree := min need a.free
  { levels := a.levels + 1, next := a.next + (need - fromFree), free := a.free - fromFree }

/-- `remove`: the leaf and (unless it was the root) the branch are released. -/
def IdAlloc.remove (a : IdAlloc) : IdAlloc :=
  if a.levels = 0 then a
  else { levels := a.levels - 1, next := a.next, free := a.free + (liveIds a.levels - liveIds (a.levels - 1)) }

/-- The allocator invariant: every id ever handed out is either live or free. -/
def IdAlloc.Wf (a : IdAlloc) : Prop := a.next = liveIds a.levels + a.free

theorem liveIds_succ (n : ℕ) : liveIds (n + 1) - liveIds n = if n = 0 then 1 else 2 := by
  cases n <;> simp [liveIds] <;> omega

theorem IdAlloc.wf_insert {a : IdAlloc} (h : a.Wf) : a.insert.Wf := by
  simp only [IdAlloc.Wf, IdAlloc.insert] at *
  unfold liveIds at *
  split_ifs at * <;> omega

theorem IdAlloc.wf_remove {a : IdAlloc} (h : a.Wf) : a.remove.Wf := by
  simp only [IdAlloc.Wf, IdAlloc.remove] at *
  split_ifs with h0
  · exact h
  · simp only []
    unfold liveIds at *
    split_ifs at * <;> omega

/-- **With recycling, the counter is the peak of live ids, not the history.**  `next` is
    `liveIds levels + free`, and `free` only holds ids that were live earlier, so `next` is
    bounded by the ids of the peak number of simultaneously stored prices. -/
theorem IdAlloc.next_le_peak {a : IdAlloc} (h : a.Wf) (peak : ℕ) (hp : a.levels ≤ peak)
    (hfree : a.free ≤ liveIds peak - liveIds a.levels) : a.next ≤ liveIds peak := by
  simp only [IdAlloc.Wf] at h
  unfold liveIds at *
  split_ifs at * <;> omega

/-- **`insert` never reverts on ids** while the peak number of simultaneous prices is below
    `2^31`: the id handed out is at most `liveIds peak ≤ 2^32 − 3`.  Holding `2^31` prices at
    once needs `2^31` storage slots, so this is unreachable. -/
theorem IdAlloc.insert_no_overflow {a : IdAlloc} (h : a.Wf) (peak : ℕ) (hp : a.levels + 1 ≤ peak)
    (hfree : a.free ≤ liveIds peak - liveIds a.levels) (hpeak : peak ≤ 2 ^ 31 - 1) :
    a.insert.next ≤ 2 ^ 32 - 1 := by
  simp only [IdAlloc.Wf, IdAlloc.insert] at *
  unfold liveIds at *
  split_ifs at * <;> omega

/-- Reachability form of the `hfree` hypothesis above: `peak` bounds every level count seen so
    far, and the free list only holds ids released from levels between `levels` and `peak`. -/
def IdAlloc.Bounded (peak : ℕ) (a : IdAlloc) : Prop :=
  a.Wf ∧ a.levels ≤ peak ∧ a.free ≤ liveIds peak - liveIds a.levels

/-- The empty `Tree` (`nextNodeId = 0`, `freeIds = []`). -/
def IdAlloc.empty : IdAlloc := { levels := 0, next := 0, free := 0 }

theorem IdAlloc.bounded_empty : IdAlloc.empty.Bounded 0 := by
  simp [IdAlloc.Bounded, IdAlloc.Wf, IdAlloc.empty, liveIds]

theorem IdAlloc.bounded_insert {a : IdAlloc} {peak : ℕ} (h : a.Bounded peak) :
    a.insert.Bounded (max peak (a.levels + 1)) := by
  simp only [IdAlloc.Bounded, IdAlloc.Wf, IdAlloc.insert] at *
  unfold liveIds at *
  split_ifs at * <;> omega

theorem IdAlloc.bounded_remove {a : IdAlloc} {peak : ℕ} (h : a.Bounded peak) :
    a.remove.Bounded peak := by
  simp only [IdAlloc.Bounded, IdAlloc.Wf, IdAlloc.remove] at *
  split_ifs with h0
  · exact h
  · simp only []
    unfold liveIds at *
    split_ifs at * <;> omega

/-- Run a sequence of new-price `insert`s (`true`) and `remove`s (`false`), tracking the peak
    number of simultaneously stored prices. -/
def IdAlloc.run : List Bool → IdAlloc × ℕ → IdAlloc × ℕ
  | [], s => s
  | true :: ops, (a, peak) => IdAlloc.run ops (a.insert, max peak (a.levels + 1))
  | false :: ops, (a, peak) => IdAlloc.run ops (a.remove, peak)

theorem IdAlloc.run_bounded (ops : List Bool) {a : IdAlloc} {peak : ℕ} (h : a.Bounded peak) :
    (IdAlloc.run ops (a, peak)).1.Bounded (IdAlloc.run ops (a, peak)).2 := by
  induction ops generalizing a peak with
  | nil => exact h
  | cons op ops ih =>
    cases op
    · exact ih (IdAlloc.bounded_remove h)
    · exact ih (IdAlloc.bounded_insert h)

/-- **From an empty tree, `nextNodeId` never exceeds the ids of the peak number of
    simultaneously stored prices**, for every insert/remove history: `next_le_peak` with its
    `hfree` hypothesis discharged. -/
theorem IdAlloc.run_next_le_peak (ops : List Bool) :
    (IdAlloc.run ops (IdAlloc.empty, 0)).1.next ≤ liveIds (IdAlloc.run ops (IdAlloc.empty, 0)).2 := by
  obtain ⟨h, hp, hfree⟩ := IdAlloc.run_bounded ops IdAlloc.bounded_empty
  exact IdAlloc.next_le_peak h _ hp hfree

end AsyncSwap
