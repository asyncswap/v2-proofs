import AsyncSwapSpec.Order

/-!
# Partial fills

Models the arithmetic of `AsyncMatching._reduceAfterMatch` and `_settleMatchedPriorityFee`:

```solidity
uint256 remainingInput   = oldInput - params.inputUsed;
uint256 remainingMinimum = params.outputReceived >= oldMinimum ? 0 : oldMinimum - params.outputReceived;
uint256 filledPriorityFee   = Math.mulDiv(oldPriorityFee, inputUsed, oldInput);
unfilledPriorityFee         = oldPriorityFee - filledPriorityFee;
if (remainingInput == 0 || remainingMinimum == 0) { /* delete, refund remainingInput */ }
```

The main result (`maker_limit_honored`) is the cumulative guarantee: over *any* sequence of
admissible legs that eventually closes an order, the maker receives at least the
`amountOutMin` they originally signed, and any unused input is refunded.
-/

namespace AsyncSwap

/-- One matched leg as seen by a single order: how much of its input was consumed and how
    much output it received. -/
structure Leg where
  used : ℕ
  received : ℕ
  deriving Repr, DecidableEq

namespace Order

/-- Priority bid donated to LPs for this leg (`filledPriorityFee`). -/
def donatedFee (o : Order) (l : Leg) : ℕ := mulDiv o.priorityFee l.used o.amountIn

/-- `_reduceAfterMatch` state update (before the delete-if-closed check). -/
def reduce (o : Order) (l : Leg) : Order :=
  { o with
    amountIn := o.amountIn - l.used
    amountOutMin := o.amountOutMin - l.received
    priorityFee := o.priorityFee - o.donatedFee l }

/-- Leg admissibility: it consumes some input, no more than is escrowed, and respects the
    order's *live* limit price `received / used ≥ amountOutMin / amountIn`.
    `Match.lean` proves both legs of every `_matchAmounts` result satisfy this. -/
def legOk (o : Order) (l : Leg) : Prop :=
  0 < l.used ∧ l.used ≤ o.amountIn ∧ l.used * o.amountOutMin ≤ l.received * o.amountIn

/-- Input accounting: consumed + remaining = original. -/
theorem reduce_amountIn (o : Order) (l : Leg) (h : l.used ≤ o.amountIn) :
    (o.reduce l).amountIn + l.used = o.amountIn := by
  simp [reduce]; omega

/-- The maker's outstanding minimum only ever shrinks by what was actually received. -/
theorem reduce_obligation (o : Order) (l : Leg) :
    o.amountOutMin ≤ (o.reduce l).amountOutMin + l.received := by
  simp [reduce]; omega

/-- While the order stays open the accounting is exact. -/
theorem reduce_obligation_exact (o : Order) (l : Leg) (h : l.received ≤ o.amountOutMin) :
    (o.reduce l).amountOutMin + l.received = o.amountOutMin := by
  simp [reduce]; omega

/-- If a single admissible leg closes the order, that leg alone delivered the full
    outstanding minimum. -/
theorem received_ge_min_of_closed (o : Order) (l : Leg) (h : o.legOk l)
    (hc : (o.reduce l).closed) : o.amountOutMin ≤ l.received := by
  obtain ⟨hpos, hle, hlim⟩ := h
  rcases hc with hc | hc
  · -- all input consumed ⇒ used = amountIn ⇒ amountIn·min ≤ received·amountIn
    simp [reduce] at hc
    have hused : l.used = o.amountIn := by omega
    rw [hused] at hlim
    have hin : 0 < o.amountIn := by omega
    rw [Nat.mul_comm o.amountIn o.amountOutMin] at hlim
    exact Nat.le_of_mul_le_mul_right hlim hin
  · simp [reduce] at hc; omega

/-- A still-open reduced order is well-formed (so `_priceKey` can be recomputed safely). -/
theorem reduce_wf_of_not_closed (o : Order) (l : Leg) (h : ¬ (o.reduce l).closed) :
    (o.reduce l).wf := by
  simp [closed, wf] at *; omega

/-- Priority fee accounting for one leg: donated + remaining = previous. -/
theorem reduce_priorityFee (o : Order) (l : Leg) (h : l.used ≤ o.amountIn) :
    (o.reduce l).priorityFee + o.donatedFee l = o.priorityFee := by
  have := mulDiv_le_of_le (a := o.priorityFee) h
  simp [reduce, donatedFee]; omega

/-- A leg that consumes all remaining input donates the whole remaining bid. -/
theorem donatedFee_full (o : Order) (l : Leg) (h : l.used = o.amountIn) (hpos : 0 < o.amountIn) :
    o.donatedFee l = o.priorityFee := by
  simp [donatedFee, h, mulDiv_self hpos]

/-! ## Sequences of legs -/

/-- Apply legs left to right. -/
def runLegs (o : Order) : List Leg → Order
  | [] => o
  | l :: ls => (o.reduce l).runLegs ls

/-- Each leg is admissible for the state it meets, and no leg touches a closed order
    (the contract deletes closed orders, so this is exactly what storage enforces). -/
def legsOk (o : Order) : List Leg → Prop
  | [] => True
  | l :: ls => ¬ o.closed ∧ o.legOk l ∧ (o.reduce l).legsOk ls

/-- Sum of bids donated across the legs. -/
def donatedFees (o : Order) : List Leg → ℕ
  | [] => 0
  | l :: ls => o.donatedFee l + (o.reduce l).donatedFees ls

/-- **Escrow accounting.** Total input consumed plus the remaining escrow equals the
    original deposit. -/
theorem runLegs_amountIn (o : Order) (ls : List Leg) (h : o.legsOk ls) :
    (o.runLegs ls).amountIn + (ls.map Leg.used).sum = o.amountIn := by
  induction ls generalizing o with
  | nil => simp [runLegs]
  | cons l ls ih =>
    obtain ⟨_, ⟨_, hle, _⟩, hrest⟩ := h
    simp only [runLegs, List.map_cons, List.sum_cons]
    have := ih (o.reduce l) hrest
    have := reduce_amountIn o l hle
    omega

/-- **Obligation accounting.** Received so far plus outstanding minimum is never below the
    original minimum, with *no* hypotheses on the legs. -/
theorem runLegs_obligation (o : Order) (ls : List Leg) :
    o.amountOutMin ≤ (o.runLegs ls).amountOutMin + (ls.map Leg.received).sum := by
  induction ls generalizing o with
  | nil => simp [runLegs]
  | cons l ls ih =>
    simp only [runLegs, List.map_cons, List.sum_cons]
    have := ih (o.reduce l)
    have := reduce_obligation o l
    omega

/-- **Maker guarantee.** If an order is closed by an admissible sequence of matches, the
    maker has received at least the minimum output they signed.  Together with
    `runLegs_amountIn` and the refund of `remainingInput` on close, the maker ends with
    `≥ amountOutMin` output *and* `amountIn − Σ used` of their input back. -/
theorem maker_limit_honored (o : Order) (ls : List Leg) (h : o.legsOk ls)
    (hc : (o.runLegs ls).closed) (hne : ls ≠ []) :
    o.amountOutMin ≤ (ls.map Leg.received).sum := by
  induction ls generalizing o with
  | nil => exact absurd rfl hne
  | cons l ls ih =>
    obtain ⟨_, hok, hrest⟩ := h
    simp only [List.map_cons, List.sum_cons]
    rcases ls with _ | ⟨l', ls'⟩
    · simp only [runLegs] at hc
      have := received_ge_min_of_closed o l hok hc
      omega
    · have h1 := ih (o.reduce l) hrest (by simpa [runLegs] using hc) (by simp)
      have h2 := reduce_obligation o l
      omega

/-- **Priority bid accounting.** Donated so far plus the remaining bid equals the original bid;
    on close the remainder is donated / forfeited too, so the bid is never refunded and never
    leaks. -/
theorem runLegs_priorityFee (o : Order) (ls : List Leg) (h : o.legsOk ls) :
    (o.runLegs ls).priorityFee + o.donatedFees ls = o.priorityFee := by
  induction ls generalizing o with
  | nil => simp [runLegs, donatedFees]
  | cons l ls ih =>
    obtain ⟨_, ⟨_, hle, _⟩, hrest⟩ := h
    simp only [runLegs, donatedFees]
    have := ih (o.reduce l) hrest
    have := reduce_priorityFee o l hle
    omega

/-- The stored remainder always fits the `uint64` slot it is cast into
    (`info.priorityFee = uint64(unfilledPriorityFee)`). -/
theorem runLegs_priorityFee_lt (o : Order) (ls : List Leg) (h : o.legsOk ls)
    (hbound : o.priorityFee ≤ maxPriorityFee) :
    (o.runLegs ls).priorityFee ≤ maxPriorityFee := by
  have := runLegs_priorityFee o ls h
  omega

end Order
end AsyncSwap
