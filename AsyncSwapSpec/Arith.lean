import Mathlib.Tactic

/-!
# Fixed-point helpers

OpenZeppelin `Math.mulDiv` with floor and ceil rounding, over unbounded ℕ.
`Math.mulDiv` computes the 512-bit product exactly and reverts if the final quotient
does not fit in 256 bits, so ℕ is a faithful model of every non-reverting execution.
-/

namespace AsyncSwap

/-- `Math.mulDiv(a, b, c)` — floor. -/
def mulDiv (a b c : ℕ) : ℕ := a * b / c

/-- `Math.mulDiv(a, b, c, Math.Rounding.Ceil)` — OZ adds one iff `mulmod(a, b, c) > 0`. -/
def mulDivCeil (a b c : ℕ) : ℕ :=
  if a * b % c = 0 then a * b / c else a * b / c + 1

theorem mulDiv_mul_le (a b c : ℕ) : mulDiv a b c * c ≤ a * b :=
  Nat.div_mul_le_self _ _

/-- Floor division by a denominator at least as large as the multiplier never exceeds `a`. -/
theorem mulDiv_le_of_le {a b c : ℕ} (h : b ≤ c) : mulDiv a b c ≤ a := by
  unfold mulDiv
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp
  · apply Nat.div_le_of_le_mul
    calc a * b ≤ a * c := Nat.mul_le_mul_left a h
      _ = c * a := Nat.mul_comm a c

/-- `mulDiv a c c = a` for `c > 0`. -/
theorem mulDiv_self {a c : ℕ} (hc : 0 < c) : mulDiv a c c = a := by
  unfold mulDiv; exact Nat.mul_div_cancel a hc

/-- Ceil rounding never under-delivers: `a·b ≤ ⌈a·b / c⌉ · c`. -/
theorem le_mulDivCeil_mul {a b c : ℕ} (hc : 0 < c) : a * b ≤ mulDivCeil a b c * c := by
  unfold mulDivCeil
  have h1 := Nat.div_add_mod (a * b) c
  have h2 := Nat.mod_lt (a * b) hc
  split_ifs with h <;> nlinarith

/-- Ceil rounding over-delivers by strictly less than one denominator unit. -/
theorem mulDivCeil_mul_lt {a b c : ℕ} (hc : 0 < c) : mulDivCeil a b c * c < a * b + c := by
  unfold mulDivCeil
  have h1 := Nat.div_add_mod (a * b) c
  have h2 := Nat.mod_lt (a * b) hc
  split_ifs with h
  · nlinarith
  · have h3 : 0 < a * b % c := Nat.pos_of_ne_zero h
    nlinarith

/-- Ceil with `b ≤ c` is bounded by `a`. -/
theorem mulDivCeil_le_of_le {a b c : ℕ} (hc : 0 < c) (h : b ≤ c) : mulDivCeil a b c ≤ a := by
  have h1 := mulDivCeil_mul_lt (a := a) (b := b) hc
  have h2 : mulDivCeil a b c * c < (a + 1) * c := by nlinarith
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right h2)

/-- A positive product has a positive ceiling. -/
theorem mulDivCeil_pos {a b c : ℕ} (hc : 0 < c) (hab : 0 < a * b) : 0 < mulDivCeil a b c := by
  apply Nat.pos_of_ne_zero
  intro h0
  have := le_mulDivCeil_mul (a := a) (b := b) hc
  rw [h0, Nat.zero_mul] at this
  omega

/-- Ceil is the *least* integer honouring the bound: `(x − 1)·c < a·b` for `x = ⌈a·b/c⌉`. -/
theorem mulDivCeil_minimal {a b c : ℕ} (hc : 0 < c) : (mulDivCeil a b c - 1) * c < a * b + 0 ∨ mulDivCeil a b c = 0 := by
  rcases Nat.eq_zero_or_pos (mulDivCeil a b c) with h0 | hpos
  · exact Or.inr h0
  · left
    have := mulDivCeil_mul_lt (a := a) (b := b) hc
    have hsub : (mulDivCeil a b c - 1) * c + c = mulDivCeil a b c * c := by
      rw [← Nat.succ_pred_eq_of_pos hpos]
      simp [Nat.succ_mul]
    omega

end AsyncSwap
