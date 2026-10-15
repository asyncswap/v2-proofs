import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# RadixPriceTree

Functional model of `src/libraries/RadixPriceTree.sol`, a Patricia (compressed binary) trie
over `uint128` price levels used as the order book's price index.

The storage layout (`nodes` mapping, `root`, `parent` pointers, `leaves` map) is abstracted
to an inductive tree.  `insert`, `remove` and `best` follow the Solidity control flow loop
for loop:

* `findLeaf`  — the first `while` in `insert`: walk to the leaf the new price would share.
* `splitBit`  — `_mostSignificantBit(price ^ leafPrice)`.
* `insertAt`  — the second `while` (`bit > splitBit` ⇒ keep descending) and the relink.
* `remove`    — a leaf's parent branch is replaced by the leaf's sibling.
* `best`      — descend right for the highest price, left for the lowest.

`solMsb` is the branch-free `_mostSignificantBit` routine written out exactly (with
`value >>= k` as `/ 2^k`) and proved equal to `Nat.log2` on its `uint128` domain.

Main results: `best_true_spec` / `best_false_spec` (the index returns the exact max / min of
the stored prices — `invariant_bestPricesAgreeWithLinearScan`), `insert_wf` / `remove_wf`
(the Patricia invariant is preserved), `mem_keys_insert` / `mem_remove` (set semantics), and
`height_le_128` (every traversal touches at most 128 branch nodes).
-/

namespace AsyncSwap

/-! ## `_mostSignificantBit` -/

/-- One `if (value >> k != 0) { value >>= k; bit += k; }` step on `(value, bit)`. -/
def msbStep (k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.1 / 2 ^ k ≠ 0 then (s.1 / 2 ^ k, s.2 + k) else s

/-- `RadixPriceTree._mostSignificantBit`, verbatim. -/
def solMsb (value : ℕ) : ℕ :=
  let s := msbStep 2 (msbStep 4 (msbStep 8 (msbStep 16 (msbStep 32 (msbStep 64 (value, 0))))))
  if s.1 / 2 ≠ 0 then s.2 + 1 else s.2

theorem msbStep_spec (k v : ℕ) (s : ℕ × ℕ)
    (h1 : s.1 = v / 2 ^ s.2) (h2 : s.1 ≠ 0) (h3 : s.1 < 2 ^ (k + k)) :
    (msbStep k s).1 = v / 2 ^ (msbStep k s).2 ∧ (msbStep k s).1 ≠ 0 ∧ (msbStep k s).1 < 2 ^ k := by
  unfold msbStep
  split_ifs with h
  · refine ⟨?_, h, ?_⟩
    · simp only
      rw [h1, Nat.div_div_eq_div_mul, ← Nat.pow_add]
    · simp only
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add]
      exact h3
  · refine ⟨h1, h2, ?_⟩
    simp only [ne_eq, not_not] at h
    by_contra hlt
    have : 1 ≤ s.1 / 2 ^ k :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mpr (by rw [one_mul]; omega)
    omega

/-- `log2` is characterised by `v / 2^b = 1`. -/
theorem log2_eq_of_div_eq_one {v b : ℕ} (hv : v ≠ 0) (hb : v / 2 ^ b = 1) : Nat.log2 v = b := by
  apply le_antisymm
  · have hlt : v < 2 ^ (b + 1) := by
      have h := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mp (show v / 2 ^ b < 2 by omega)
      rw [Nat.pow_succ]; linarith
    exact Nat.lt_succ_iff.mp ((Nat.log2_lt hv).mpr hlt)
  · have hle : 2 ^ b ≤ v := by
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos b)).mp (show 1 ≤ v / 2 ^ b by omega)
      rwa [one_mul] at this
    exact (Nat.le_log2 hv).mpr hle

/-- The Solidity routine computes `⌊log₂ value⌋` for every non-zero `uint128`. -/
theorem solMsb_eq_log2 (v : ℕ) (hv : v ≠ 0) (hlt : v < 2 ^ 128) : solMsb v = Nat.log2 v := by
  have s0 : ((v, 0) : ℕ × ℕ).1 = v / 2 ^ ((v, 0) : ℕ × ℕ).2 := by simp
  have h64 := msbStep_spec 64 v (v, 0) s0 hv (by simpa using hlt)
  have h32 := msbStep_spec 32 v _ h64.1 h64.2.1 (by simpa using h64.2.2)
  have h16 := msbStep_spec 16 v _ h32.1 h32.2.1 (by simpa using h32.2.2)
  have h8 := msbStep_spec 8 v _ h16.1 h16.2.1 (by simpa using h16.2.2)
  have h4 := msbStep_spec 4 v _ h8.1 h8.2.1 (by simpa using h8.2.2)
  have h2 := msbStep_spec 2 v _ h4.1 h4.2.1 (by simpa using h4.2.2)
  obtain ⟨e1, e2, e3⟩ := h2
  norm_num at e3
  unfold solMsb
  simp only
  split_ifs with h
  · refine (log2_eq_of_div_eq_one hv ?_).symm
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← e1]
    omega
  · refine (log2_eq_of_div_eq_one hv ?_).symm
    rw [← e1]
    simp only [ne_eq, not_not] at h
    omega

/-! ## Bit lemmas for the split bit -/

/-- `_mostSignificantBit(p ^ q)`. -/
def splitBit (p q : ℕ) : ℕ := Nat.log2 (p ^^^ q)

theorem testBit_log2 {x : ℕ} (hx : x ≠ 0) : x.testBit (Nat.log2 x) = true := by
  have h1 := Nat.log2_self_le hx
  have h2 := @Nat.lt_log2_self x
  have hdiv : x / 2 ^ Nat.log2 x = 1 := by
    apply le_antisymm
    · have : x < 2 * 2 ^ Nat.log2 x := by rw [Nat.pow_succ] at h2; linarith
      exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr this)
    · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by rw [one_mul]; exact h1)
  rw [Nat.testBit_eq_decide_div_mod_eq, hdiv]
  decide

theorem testBit_gt_log2 {x i : ℕ} (hi : Nat.log2 x < i) : x.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · exact Nat.two_pow_pos i
  · calc x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi

/-- `p` and `q` differ at the split bit. -/
theorem splitBit_ne {p q : ℕ} (h : p ≠ q) : p.testBit (splitBit p q) ≠ q.testBit (splitBit p q) := by
  have hx : p ^^^ q ≠ 0 := by
    intro h0
    apply h
    have := congrArg (· ^^^ q) h0
    simpa [Nat.xor_assoc] using this
  have := testBit_log2 hx
  rw [Nat.testBit_xor] at this
  unfold splitBit
  revert this
  cases p.testBit (Nat.log2 (p ^^^ q)) <;> cases q.testBit (Nat.log2 (p ^^^ q)) <;> simp

/-- `p` and `q` agree on every bit above the split bit. -/
theorem splitBit_agree (p q : ℕ) {i : ℕ} (hi : splitBit p q < i) : p.testBit i = q.testBit i := by
  have := testBit_gt_log2 (x := p ^^^ q) hi
  rw [Nat.testBit_xor] at this
  revert this
  cases p.testBit i <;> cases q.testBit i <;> simp

/-! ## The trie -/

inductive Trie
  | leaf (price : ℕ)
  | branch (bit : ℕ) (left right : Trie)
  deriving Repr, DecidableEq

namespace Trie

/-- Prices stored in the trie. -/
def keys : Trie → Finset ℕ
  | leaf p => {p}
  | branch _ l r => l.keys ∪ r.keys

/-- First loop of `insert`: walk by the new price's bits down to a leaf. -/
def findLeaf (p : ℕ) : Trie → ℕ
  | leaf q => q
  | branch b l r => if p.testBit b then r.findLeaf p else l.findLeaf p

/-- Second loop of `insert` + relink: keep descending while `bit > splitBit`, then put a new
    branch at `splitBit` with the current node and the new leaf as children. -/
def insertAt (p split : ℕ) : Trie → Trie
  | leaf q => if p.testBit split then branch split (leaf q) (leaf p) else branch split (leaf p) (leaf q)
  | branch b l r =>
      if split < b then
        if p.testBit b then branch b l (r.insertAt p split) else branch b (l.insertAt p split) r
      else if p.testBit split then branch split (branch b l r) (leaf p)
      else branch split (leaf p) (branch b l r)

/-- `RadixPriceTree.insert` on a non-empty tree.  Returns the tree unchanged when the price
    is already present (`created == false`). -/
def insert (p : ℕ) (t : Trie) : Trie :=
  if p ∈ t.keys then t else t.insertAt p (splitBit p (t.findLeaf p))

/-- `RadixPriceTree.remove`: the removed leaf's parent branch is replaced by its sibling;
    `none` means the tree became empty (`root = 0`). -/
def remove (p : ℕ) : Trie → Option Trie
  | leaf q => if q = p then none else some (leaf q)
  | branch b l r =>
      if p.testBit b then
        match r.remove p with
        | none => some l
        | some r' => some (branch b l r')
      else
        match l.remove p with
        | none => some r
        | some l' => some (branch b l' r)

/-- `RadixPriceTree.best`: rightmost leaf for `highest`, leftmost otherwise. -/
def best (highest : Bool) : Trie → ℕ
  | leaf p => p
  | branch _ l r => if highest then r.best highest else l.best highest

/-- Number of branch nodes on the longest root-to-leaf path. -/
def height : Trie → ℕ
  | leaf _ => 0
  | branch _ l r => max l.height r.height + 1

/-- The Patricia invariant: at a branch with bit `b`, every price on the left has bit `b`
    clear, every price on the right has it set, and all prices below the branch agree on
    every bit above `b`. -/
inductive Wf : Trie → Prop
  | leaf (p : ℕ) : Wf (leaf p)
  | branch {b : ℕ} {l r : Trie} :
      Wf l → Wf r →
      (∀ q ∈ l.keys, q.testBit b = false) →
      (∀ q ∈ r.keys, q.testBit b = true) →
      (∀ q ∈ l.keys ∪ r.keys, ∀ q' ∈ l.keys ∪ r.keys, ∀ i, b < i → q.testBit i = q'.testBit i) →
      Wf (branch b l r)

/-! ### Basic facts -/

theorem keys_nonempty (t : Trie) : t.keys.Nonempty := by
  induction t with
  | leaf p => simp [keys]
  | branch b l r ihl _ => exact ihl.mono (by simp [keys])

theorem findLeaf_mem (p : ℕ) (t : Trie) : t.findLeaf p ∈ t.keys := by
  induction t with
  | leaf q => simp [findLeaf, keys]
  | branch b l r ihl ihr =>
    simp only [findLeaf, keys]
    split_ifs
    · exact Finset.mem_union_right _ ihr
    · exact Finset.mem_union_left _ ihl

theorem mem_keys_insertAt (p split q : ℕ) (t : Trie) :
    q ∈ (t.insertAt p split).keys ↔ q ∈ t.keys ∨ q = p := by
  induction t with
  | leaf x => simp only [insertAt]; split_ifs <;> simp [keys, or_comm]
  | branch b l r ihl ihr =>
    simp only [insertAt]
    split_ifs <;> simp [keys, ihl, ihr] <;> tauto

theorem mem_keys_insert (p q : ℕ) (t : Trie) :
    q ∈ (t.insert p).keys ↔ q ∈ t.keys ∨ q = p := by
  unfold insert
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (hq | rfl)
      · exact hq
      · exact h
  · exact mem_keys_insertAt _ _ _ _

/-- A price with a clear bit is below any price with that bit set, provided they agree above. -/
theorem lt_of_bit {x y b : ℕ} (hx : x.testBit b = false) (hy : y.testBit b = true)
    (hagree : ∀ i, b < i → x.testBit i = y.testBit i) : x < y :=
  Nat.lt_of_testBit b hx hy hagree

/-! ### `best` returns the exact extremum -/

/-- `best(true)` is the maximum stored price (`invariant_bestPricesAgreeWithLinearScan`). -/
theorem best_true_spec {t : Trie} (hw : Wf t) :
    t.best true ∈ t.keys ∧ ∀ q ∈ t.keys, q ≤ t.best true := by
  induction hw with
  | leaf p => simp [best, keys]
  | @branch b l r _ _ h1 h2 h3 _ ihr =>
    simp only [best, keys, ↓reduceIte]
    obtain ⟨hmem, hmax⟩ := ihr
    refine ⟨Finset.mem_union_right _ hmem, ?_⟩
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (lt_of_bit (h1 q hq) (h2 _ hmem)
        (fun i hi => h3 q (Finset.mem_union_left _ hq) _ (Finset.mem_union_right _ hmem) i hi)).le
    · exact hmax q hq

/-- `best(false)` is the minimum stored price. -/
theorem best_false_spec {t : Trie} (hw : Wf t) :
    t.best false ∈ t.keys ∧ ∀ q ∈ t.keys, t.best false ≤ q := by
  induction hw with
  | leaf p => simp [best, keys]
  | @branch b l r _ _ h1 h2 h3 ihl _ =>
    simp only [best, keys, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hmem, hmin⟩ := ihl
    refine ⟨Finset.mem_union_left _ hmem, ?_⟩
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hmin q hq
    · exact (lt_of_bit (h1 _ hmem) (h2 q hq)
        (fun i hi => h3 _ (Finset.mem_union_left _ hmem) q (Finset.mem_union_right _ hq) i hi)).le

theorem best_true_eq_max' {t : Trie} (hw : Wf t) :
    t.best true = t.keys.max' (keys_nonempty t) := by
  obtain ⟨hmem, hmax⟩ := best_true_spec hw
  exact le_antisymm (Finset.le_max' _ _ hmem) (Finset.max'_le _ _ _ hmax)

theorem best_false_eq_min' {t : Trie} (hw : Wf t) :
    t.best false = t.keys.min' (keys_nonempty t) := by
  obtain ⟨hmem, hmin⟩ := best_false_spec hw
  exact le_antisymm (Finset.le_min' _ _ _ hmin) (Finset.min'_le _ _ hmem)

/-! ### Insert preserves the invariant -/

theorem findLeaf_branch_bit {p b : ℕ} {l r : Trie}
    (h1 : ∀ q ∈ l.keys, q.testBit b = false) (h2 : ∀ q ∈ r.keys, q.testBit b = true) :
    ((branch b l r).findLeaf p).testBit b = p.testBit b := by
  simp only [findLeaf]
  cases hp : p.testBit b
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact h1 _ (findLeaf_mem p l)
  · simp only [↓reduceIte]; exact h2 _ (findLeaf_mem p r)

theorem insertAt_wf {t : Trie} (hw : Wf t) (p split : ℕ)
    (hagree : ∀ i, split < i → p.testBit i = (t.findLeaf p).testBit i)
    (hdiff : p.testBit split ≠ (t.findLeaf p).testBit split) :
    Wf (t.insertAt p split) := by
  induction hw with
  | leaf q =>
    simp only [findLeaf] at hagree hdiff
    have hq : q.testBit split = !p.testBit split := by
      revert hdiff; cases p.testBit split <;> cases q.testBit split <;> simp
    have hpair : ∀ x y : ℕ, (x = q ∨ x = p) → (y = q ∨ y = p) → ∀ i, split < i →
        x.testBit i = y.testBit i := by
      intro x y hx hy i hi
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [hagree i hi]
    simp only [insertAt]
    by_cases hp : p.testBit split = true
    · simp only [hp, ↓reduceIte]
      refine Wf.branch (Wf.leaf q) (Wf.leaf p) ?_ ?_ ?_
      · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; simp [hq, hp]
      · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; exact hp
      · intro x hx y hy i hi
        simp only [keys, Finset.mem_union, Finset.mem_singleton] at hx hy
        exact hpair x y hx hy i hi
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      refine Wf.branch (Wf.leaf p) (Wf.leaf q) ?_ ?_ ?_
      · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; simpa using hp
      · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; simp [hq, hp]
      · intro x hx y hy i hi
        simp only [keys, Finset.mem_union, Finset.mem_singleton] at hx hy
        exact hpair x y hx.symm hy.symm i hi
  | @branch b l r hl hr h1 h2 h3 ihl ihr =>
    -- the leaf found below this branch sits on `p`'s side, so it agrees with `p` at bit `b`
    have hbit := findLeaf_branch_bit (p := p) h1 h2
    have hq0 := findLeaf_mem p (branch b l r)
    -- every key below this branch agrees with `p` above `max b split`
    have hp_agree : ∀ x ∈ l.keys ∪ r.keys, ∀ i, b < i → split < i → p.testBit i = x.testBit i :=
      fun x hx i hbi hsi => (hagree i hsi).trans (h3 _ hq0 x hx i hbi)
    have key : ∀ x y : ℕ, (x ∈ l.keys ∨ x ∈ r.keys ∨ x = p) → (y ∈ l.keys ∨ y ∈ r.keys ∨ y = p) →
        ∀ i, b < i → split < i → x.testBit i = y.testBit i := by
      intro x y hx hy i hbi hsi
      have hx' : x = p ∨ x ∈ l.keys ∪ r.keys := by
        rcases hx with h | h | h <;> simp [h]
      have hy' : y = p ∨ y ∈ l.keys ∪ r.keys := by
        rcases hy with h | h | h <;> simp [h]
      rcases hx' with rfl | hx' <;> rcases hy' with rfl | hy'
      · rfl
      · exact hp_agree y hy' i hbi hsi
      · exact (hp_agree x hx' i hbi hsi).symm
      · exact h3 x hx' y hy' i hbi
    simp only [insertAt]
    by_cases hs : split < b
    · simp only [hs, ↓reduceIte]
      by_cases hp : p.testBit b = true
      · -- descend right
        simp only [hp, ↓reduceIte]
        simp only [findLeaf, hp, ↓reduceIte] at hagree hdiff
        refine Wf.branch hl (ihr hagree hdiff) h1 ?_ ?_
        · intro x hx
          rcases (mem_keys_insertAt _ _ _ _).mp hx with hx | rfl
          · exact h2 x hx
          · exact hp
        · intro x hx y hy i hi
          have hx' := Finset.mem_union.mp hx
          have hy' := Finset.mem_union.mp hy
          simp only [mem_keys_insertAt] at hx' hy'
          exact key x y hx' hy' i hi (by omega)
      · -- descend left
        simp only [hp, Bool.false_eq_true, ↓reduceIte]
        simp only [findLeaf, hp, Bool.false_eq_true, ↓reduceIte] at hagree hdiff
        refine Wf.branch (ihl hagree hdiff) hr ?_ h2 ?_
        · intro x hx
          rcases (mem_keys_insertAt _ _ _ _).mp hx with hx | rfl
          · exact h1 x hx
          · simpa using hp
        · intro x hx y hy i hi
          have hx' := Finset.mem_union.mp hx
          have hy' := Finset.mem_union.mp hy
          simp only [mem_keys_insertAt] at hx' hy'
          exact key x y (by rcases hx' with (h | h) | h <;> simp [h])
            (by rcases hy' with (h | h) | h <;> simp [h]) i hi (by omega)
    · -- stop here: `b ≤ split`, and `b ≠ split` because `p` and the found leaf agree at `b`
      simp only [hs, ↓reduceIte]
      have hbs : b < split := by
        rcases Nat.lt_or_ge b split with h | h
        · exact h
        · exfalso
          have : b = split := by omega
          subst this
          exact hdiff hbit.symm
      -- every key below this branch has the opposite split bit to `p`
      have hopp : ∀ x ∈ l.keys ∪ r.keys, x.testBit split = !p.testBit split := by
        intro x hx
        have := h3 _ hq0 x hx split hbs
        rw [← this]
        revert hdiff
        cases p.testBit split <;> cases ((branch b l r).findLeaf p).testBit split <;> simp
      have hall : ∀ x y : ℕ, (x ∈ l.keys ∨ x ∈ r.keys ∨ x = p) → (y ∈ l.keys ∨ y ∈ r.keys ∨ y = p) →
          ∀ i, split < i → x.testBit i = y.testBit i :=
        fun x y hx hy i hi => key x y hx hy i (by omega) hi
      by_cases hp' : p.testBit split = true
      · simp only [hp', ↓reduceIte]
        refine Wf.branch (Wf.branch hl hr h1 h2 h3) (Wf.leaf p) ?_ ?_ ?_
        · intro x hx; rw [hopp x hx, hp']; rfl
        · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; exact hp'
        · intro x hx y hy i hi
          simp only [keys, Finset.mem_union, Finset.mem_singleton] at hx hy
          exact hall x y (by rcases hx with (h | h) | h <;> simp [h])
            (by rcases hy with (h | h) | h <;> simp [h]) i hi
      · simp only [hp', Bool.false_eq_true, ↓reduceIte]
        have hp'' : p.testBit split = false := by simpa using hp'
        refine Wf.branch (Wf.leaf p) (Wf.branch hl hr h1 h2 h3) ?_ ?_ ?_
        · intro x hx; simp only [keys, Finset.mem_singleton] at hx; subst hx; exact hp''
        · intro x hx; rw [hopp x hx, hp'']; rfl
        · intro x hx y hy i hi
          simp only [keys, Finset.mem_union, Finset.mem_singleton] at hx hy
          exact hall x y (by rcases hx with h | h | h <;> simp [h])
            (by rcases hy with h | h | h <;> simp [h]) i hi

/-- **Insert preserves the Patricia invariant.** -/
theorem insert_wf {t : Trie} (hw : Wf t) (p : ℕ) : Wf (t.insert p) := by
  unfold insert
  split_ifs with h
  · exact hw
  · have hne : p ≠ t.findLeaf p := fun e => h (e ▸ findLeaf_mem p t)
    exact insertAt_wf hw p _ (fun i hi => splitBit_agree _ _ hi) (splitBit_ne hne)

/-! ### Remove -/

def keysOpt : Option Trie → Finset ℕ
  | none => ∅
  | some t => t.keys

theorem remove_keys_subset (p : ℕ) (t : Trie) : keysOpt (t.remove p) ⊆ t.keys := by
  induction t with
  | leaf q =>
    simp only [remove]; split_ifs <;> simp [keysOpt, keys]
  | branch b l r ihl ihr =>
    simp only [remove]
    split_ifs
    · cases h : r.remove p with
      | none => simp [keysOpt, keys]
      | some r' =>
        rw [h] at ihr
        intro q hq
        simp only [keysOpt, keys, Finset.mem_union] at hq ⊢
        exact hq.imp id (fun hq => ihr hq)
    · cases h : l.remove p with
      | none => simp [keysOpt, keys]
      | some l' =>
        rw [h] at ihl
        intro q hq
        simp only [keysOpt, keys, Finset.mem_union] at hq ⊢
        exact hq.imp (fun hq => ihl hq) id

/-- **Remove has exact set semantics** on a well-formed trie. -/
theorem mem_remove {t : Trie} (hw : Wf t) (p q : ℕ) :
    q ∈ keysOpt (t.remove p) ↔ q ∈ t.keys ∧ q ≠ p := by
  induction hw with
  | leaf x =>
    simp only [remove, keys]
    split_ifs with h
    · subst h; simp [keysOpt]
    · simp only [keysOpt, keys, Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, h⟩
      · exact fun h => h.1
  | @branch b l r _ _ h1 h2 _ ihl ihr =>
    simp only [remove]
    split_ifs with hb
    · have hl_ne : ∀ x ∈ l.keys, x ≠ p := fun x hx hxp => by
        subst hxp; rw [h1 x hx] at hb; exact Bool.false_ne_true hb
      cases h : r.remove p with
      | none =>
        rw [h] at ihr
        simp only [keysOpt, keys, Finset.mem_union, Finset.notMem_empty, false_iff] at ihr ⊢
        constructor
        · intro hq; exact ⟨Or.inl hq, hl_ne q hq⟩
        · rintro ⟨hq | hq, hqp⟩
          · exact hq
          · exact absurd ⟨hq, hqp⟩ ihr
      | some r' =>
        rw [h] at ihr
        simp only [keysOpt, keys, Finset.mem_union] at ihr ⊢
        constructor
        · rintro (hq | hq)
          · exact ⟨Or.inl hq, hl_ne q hq⟩
          · exact ⟨Or.inr (ihr.mp hq).1, (ihr.mp hq).2⟩
        · rintro ⟨hq | hq, hqp⟩
          · exact Or.inl hq
          · exact Or.inr (ihr.mpr ⟨hq, hqp⟩)
    · have hr_ne : ∀ x ∈ r.keys, x ≠ p := fun x hx hxp => by
        subst hxp; rw [h2 x hx] at hb; exact hb rfl
      cases h : l.remove p with
      | none =>
        rw [h] at ihl
        simp only [keysOpt, keys, Finset.mem_union, Finset.notMem_empty, false_iff] at ihl ⊢
        constructor
        · intro hq; exact ⟨Or.inr hq, hr_ne q hq⟩
        · rintro ⟨hq | hq, hqp⟩
          · exact absurd ⟨hq, hqp⟩ ihl
          · exact hq
      | some l' =>
        rw [h] at ihl
        simp only [keysOpt, keys, Finset.mem_union] at ihl ⊢
        constructor
        · rintro (hq | hq)
          · exact ⟨Or.inl (ihl.mp hq).1, (ihl.mp hq).2⟩
          · exact ⟨Or.inr hq, hr_ne q hq⟩
        · rintro ⟨hq | hq, hqp⟩
          · exact Or.inl (ihl.mpr ⟨hq, hqp⟩)
          · exact Or.inr hq

/-- Removing an absent price is a no-op (the contract reverts with `PriceLevelMissing`
    instead, via the `leaves` map; the tree itself is untouched either way). -/
theorem remove_of_not_mem {t : Trie} (hw : Wf t) {p : ℕ} (hp : p ∉ t.keys) :
    t.remove p = some t := by
  induction hw with
  | leaf x => simp only [remove, keys, Finset.mem_singleton] at hp ⊢; simp [Ne.symm hp]
  | @branch b l r _ _ _ _ _ ihl ihr =>
    simp only [keys, Finset.mem_union, not_or] at hp
    simp only [remove]
    split_ifs
    · rw [ihr hp.2]
    · rw [ihl hp.1]

/-- The tree only becomes empty when it was the single leaf being removed. -/
theorem remove_eq_none_iff (t : Trie) (p : ℕ) : t.remove p = none ↔ t = leaf p := by
  cases t with
  | leaf q => simp only [remove]; split_ifs with h <;> simp [h]
  | branch b l r =>
    simp only [remove, reduceCtorEq, iff_false]
    split_ifs <;> cases r.remove p <;> cases l.remove p <;> simp

/-- **Remove preserves the Patricia invariant.** -/
theorem remove_wf {t : Trie} (hw : Wf t) (p : ℕ) : ∀ t', t.remove p = some t' → Wf t' := by
  induction hw with
  | leaf x =>
    intro t' h
    simp only [remove] at h
    split_ifs at h
    simp only [Option.some.injEq] at h; subst h; exact Wf.leaf x
  | @branch b l r hl hr h1 h2 h3 ihl ihr =>
    intro t' h
    simp only [remove] at h
    split_ifs at h with hb
    · cases hrem : r.remove p with
      | none => rw [hrem] at h; simp only [Option.some.injEq] at h; subst h; exact hl
      | some r' =>
        rw [hrem] at h; simp only [Option.some.injEq] at h; subst h
        have hsub : r'.keys ⊆ r.keys := by
          have := remove_keys_subset p r; rwa [hrem] at this
        refine Wf.branch hl (ihr r' hrem) h1 (fun q hq => h2 q (hsub hq)) ?_
        intro x hx y hy i hi
        exact h3 x (Finset.union_subset_union_right hsub hx) y
          (Finset.union_subset_union_right hsub hy) i hi
    · cases hrem : l.remove p with
      | none => rw [hrem] at h; simp only [Option.some.injEq] at h; subst h; exact hr
      | some l' =>
        rw [hrem] at h; simp only [Option.some.injEq] at h; subst h
        have hsub : l'.keys ⊆ l.keys := by
          have := remove_keys_subset p l; rwa [hrem] at this
        refine Wf.branch (ihl l' hrem) hr (fun q hq => h1 q (hsub hq)) h2 ?_
        intro x hx y hy i hi
        exact h3 x (Finset.union_subset_union_left hsub hx) y
          (Finset.union_subset_union_left hsub hy) i hi

/-! ### Depth bound -/

/-- If all stored prices agree on every bit `≥ n`, the trie has at most `n` branch levels. -/
theorem height_le {t : Trie} (hw : Wf t) :
    ∀ n, (∀ q ∈ t.keys, ∀ q' ∈ t.keys, ∀ i, n ≤ i → q.testBit i = q'.testBit i) → t.height ≤ n := by
  induction hw with
  | leaf p => intro n _; simp [height]
  | @branch b l r _ _ h1 h2 h3 ihl ihr =>
    intro n hn
    have hb : b < n := by
      obtain ⟨x, hx⟩ := keys_nonempty l
      obtain ⟨y, hy⟩ := keys_nonempty r
      by_contra hnb
      have := hn x (by simp [keys, hx]) y (by simp [keys, hy]) b (by omega)
      rw [h1 x hx, h2 y hy] at this
      exact Bool.false_ne_true this
    have hl' : l.height ≤ b := ihl b (fun q hq q' hq' i hi => by
      rcases Nat.eq_or_lt_of_le hi with rfl | hi
      · rw [h1 q hq, h1 q' hq']
      · exact h3 q (by simp [hq]) q' (by simp [hq']) i hi)
    have hr' : r.height ≤ b := ihr b (fun q hq q' hq' i hi => by
      rcases Nat.eq_or_lt_of_le hi with rfl | hi
      · rw [h2 q hq, h2 q' hq']
      · exact h3 q (by simp [hq]) q' (by simp [hq']) i hi)
    simp only [height]; omega

/-- **Every traversal touches at most 128 branch nodes** when all prices are `uint128`. -/
theorem height_le_128 {t : Trie} (hw : Wf t) (hkeys : ∀ q ∈ t.keys, q < 2 ^ 128) :
    t.height ≤ 128 := by
  apply height_le hw
  intro q hq q' hq' i hi
  have hb : ∀ x ∈ t.keys, x.testBit i = false := fun x hx =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (hkeys x hx) (Nat.pow_le_pow_right (by norm_num) hi))
  rw [hb q hq, hb q' hq']

end Trie

/-! ## The index as stored in `RadixPriceTree.Tree` (`root == 0` ⇔ empty) -/

/-- `Tree` abstracted: `none` is the empty index. -/
abbrev PriceIndex := Option Trie

namespace PriceIndex

def keys : PriceIndex → Finset ℕ
  | none => ∅
  | some t => t.keys

def Wf : PriceIndex → Prop
  | none => True
  | some t => t.Wf

/-- `insert`: a fresh leaf becomes the root of an empty tree. -/
def insert (p : ℕ) : PriceIndex → PriceIndex
  | none => some (Trie.leaf p)
  | some t => some (t.insert p)

/-- `remove`: `PriceLevelMissing` is modelled as a no-op on the tree. -/
def remove (p : ℕ) : PriceIndex → PriceIndex
  | none => none
  | some t => t.remove p

/-- `best(highest)`: `(found, price)` with `(false, 0)` on an empty tree. -/
def best (highest : Bool) : PriceIndex → Bool × ℕ
  | none => (false, 0)
  | some t => (true, t.best highest)

theorem mem_keys_insert (p q : ℕ) (ix : PriceIndex) :
    q ∈ (ix.insert p).keys ↔ q ∈ ix.keys ∨ q = p := by
  cases ix with
  | none => simp [insert, keys, Trie.keys]
  | some t => simp [insert, keys, Trie.mem_keys_insert]

theorem insert_wf {ix : PriceIndex} (hw : ix.Wf) (p : ℕ) : (ix.insert p).Wf := by
  cases ix with
  | none => exact Trie.Wf.leaf p
  | some t => exact Trie.insert_wf hw p

theorem mem_remove {ix : PriceIndex} (hw : ix.Wf) (p q : ℕ) :
    q ∈ (ix.remove p).keys ↔ q ∈ ix.keys ∧ q ≠ p := by
  cases ix with
  | none => simp [remove, keys]
  | some t => exact Trie.mem_remove hw p q

theorem remove_wf {ix : PriceIndex} (hw : ix.Wf) (p : ℕ) : (ix.remove p).Wf := by
  cases ix with
  | none => trivial
  | some t =>
    show Wf (t.remove p)
    cases h : t.remove p with
    | none => trivial
    | some t' => exact Trie.remove_wf hw p t' h

/-- `best` reports `found` exactly when the index is non-empty, and then the exact extremum:
    the Lean form of `invariant_bestPricesAgreeWithLinearScan`. -/
theorem best_spec {ix : PriceIndex} (hw : ix.Wf) (highest : Bool) :
    ((ix.best highest).1 = true ↔ ix.keys.Nonempty) ∧
    ((ix.best highest).1 = true →
      (ix.best highest).2 ∈ ix.keys ∧
      ∀ q ∈ ix.keys, if highest then q ≤ (ix.best highest).2 else (ix.best highest).2 ≤ q) := by
  cases ix with
  | none => simp [best, keys]
  | some t =>
    refine ⟨by simp [best, keys, Trie.keys_nonempty], fun _ => ?_⟩
    simp only [best, keys]
    cases highest
    · obtain ⟨hmem, hmin⟩ := Trie.best_false_spec hw
      exact ⟨hmem, fun q hq => by simpa using hmin q hq⟩
    · obtain ⟨hmem, hmax⟩ := Trie.best_true_spec hw
      exact ⟨hmem, fun q hq => by simpa using hmax q hq⟩

end PriceIndex
end AsyncSwap
