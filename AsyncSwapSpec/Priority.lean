import AsyncSwapSpec.RadixTree
import AsyncSwapSpec.Order

/-!
# Price-time priority (decision 1: bid first, then FIFO)

Models how `AsyncFiller` orders the resting orders at one price level and how
`matchIncoming` / `matchBook` pick the level, and proves the maintainer's chosen rule:

* **Across levels**: the book's bid side is a `RadixPriceTree` of price keys, the ask side
  another; `bestOrder` takes `bids.best(true)` (highest bid) and `asks.best(false)` (lowest
  ask).  `AsyncSwapSpec/RadixTree.lean` proves `best` is the exact extremum, so the matched
  level is always the best price (`best_bid_is_max`, `best_ask_is_min`).
* **Within a level, `PriorityFee` mode**: each resting order is indexed by
  `_priorityKey(fee, sequence) = (fee << 64) | (maxUint64 − sequence)` in a `RadixPriceTree`,
  and `bestAtPrice` takes `priorityOrders.best(true)`.  `priorityKey_lt_iff` shows the key
  order is exactly "higher bid first, equal bids by earlier sequence", so `bestAtPrice`
  returns the highest-bid, then earliest, order (`bestAtPrice_priority`).
* **Within a level, `FIFO` mode**: `_append` adds at the tail and the level is a queue; with
  sequences assigned by `++nextSequence`, the head is the earliest order (`fifo_head_earliest`).
* **Reprice loses time priority**: `updatePrice` re-appends with `sequence = ++nextSequence`,
  which is larger than every live sequence (`reprice_sequence_last`).
-/

namespace AsyncSwap

/-! ## The priority key -/

def maxUint64 : ℕ := 2 ^ 64 - 1

/-- `AsyncFiller._priorityKey(priorityFee, sequence)` for `priorityFee, sequence < 2^64`:
    `(fee << 64) | (maxUint64 − sequence)`; the OR is a sum because the low word is < 2^64. -/
def priorityKey (fee seq : ℕ) : ℕ := fee * 2 ^ 64 + (maxUint64 - seq)

theorem priorityKey_lt_two_pow_128 {fee seq : ℕ} (hf : fee < 2 ^ 64) : priorityKey fee seq < 2 ^ 128 := by
  unfold priorityKey maxUint64
  have : fee * 2 ^ 64 ≤ (2 ^ 64 - 1) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The key order is lexicographic: higher bid first, then earlier sequence.** -/
theorem priorityKey_lt_iff {f1 s1 f2 s2 : ℕ} (hs1 : s1 ≤ maxUint64) (hs2 : s2 ≤ maxUint64) :
    priorityKey f1 s1 < priorityKey f2 s2 ↔ f1 < f2 ∨ (f1 = f2 ∧ s2 < s1) := by
  unfold priorityKey maxUint64 at *
  constructor
  · intro h
    rcases Nat.lt_trichotomy f1 f2 with hf | hf | hf
    · exact Or.inl hf
    · subst hf; right; exact ⟨rfl, by omega⟩
    · exfalso
      have : f2 * 2 ^ 64 + 2 ^ 64 ≤ f1 * 2 ^ 64 := by
        have := Nat.mul_le_mul_right (2 ^ 64) hf; rw [Nat.succ_mul] at this; exact this
      omega
  · rintro (hf | ⟨rfl, hs⟩)
    · have : f1 * 2 ^ 64 + 2 ^ 64 ≤ f2 * 2 ^ 64 := by
        have := Nat.mul_le_mul_right (2 ^ 64) hf; rw [Nat.succ_mul] at this; exact this
      omega
    · omega

/-- Distinct sequences give distinct keys (so the radix tree never collides). -/
theorem priorityKey_injective {f1 s1 f2 s2 : ℕ} (hs1 : s1 ≤ maxUint64) (hs2 : s2 ≤ maxUint64)
    (h : priorityKey f1 s1 = priorityKey f2 s2) : f1 = f2 ∧ s1 = s2 := by
  have h1 : ¬ priorityKey f1 s1 < priorityKey f2 s2 := by omega
  have h2 : ¬ priorityKey f2 s2 < priorityKey f1 s1 := by omega
  rw [priorityKey_lt_iff hs1 hs2] at h1
  rw [priorityKey_lt_iff hs2 hs1] at h2
  simp only [not_or, not_and, not_lt] at h1 h2
  obtain ⟨hf1, hs1'⟩ := h1
  obtain ⟨hf2, hs2'⟩ := h2
  have hf : f1 = f2 := le_antisymm hf2 hf1
  subst hf
  exact ⟨rfl, le_antisymm (hs1' rfl) (hs2' rfl)⟩

/-! ## A price level in `PriorityFee` mode -/

/-- A resting order as the level sees it. -/
structure Resting where
  id : ℕ
  fee : ℕ
  seq : ℕ
  deriving DecidableEq, Repr

/-- "`a` ranks before `b`": higher bid, or equal bid and earlier sequence. -/
def ranksBefore (a b : Resting) : Prop := a.fee > b.fee ∨ (a.fee = b.fee ∧ a.seq < b.seq)

/-- `PriceLevel.priorityOrders` and `priorityOrderIds`, abstracted: the set of resting orders
    (all with distinct sequences and in-range bids / sequences) and the key trie over them. -/
structure PriorityLevel where
  orders : Finset Resting
  tree : Trie
  keys_eq : tree.keys = orders.image (fun r => priorityKey r.fee r.seq)
  wf : tree.Wf
  bounded : ∀ r ∈ orders, r.fee < 2 ^ 64 ∧ r.seq ≤ maxUint64
  seq_inj : ∀ a ∈ orders, ∀ b ∈ orders, a.seq = b.seq → a = b

namespace PriorityLevel

/-- `bestAtPrice` in `PriorityFee` mode: the order whose key is `priorityOrders.best(true)`. -/
noncomputable def best (L : PriorityLevel) (_h : L.orders.Nonempty) : Resting :=
  Classical.choose (show ∃ r ∈ L.orders, priorityKey r.fee r.seq = L.tree.best true from by
    have hmem := (Trie.best_true_spec L.wf).1
    rw [L.keys_eq, Finset.mem_image] at hmem
    obtain ⟨r, hr, hk⟩ := hmem
    exact ⟨r, hr, hk⟩)

theorem best_mem (L : PriorityLevel) (h : L.orders.Nonempty) : L.best h ∈ L.orders :=
  (Classical.choose_spec (p := fun r => r ∈ L.orders ∧ priorityKey r.fee r.seq = L.tree.best true) _).1

theorem best_key (L : PriorityLevel) (h : L.orders.Nonempty) :
    priorityKey (L.best h).fee (L.best h).seq = L.tree.best true :=
  (Classical.choose_spec (p := fun r => r ∈ L.orders ∧ priorityKey r.fee r.seq = L.tree.best true) _).2

/-- **Bid first, then FIFO.**  `bestAtPrice` returns an order that no other resting order
    out-ranks: every other order has a strictly lower bid, or the same bid and a later
    sequence. -/
theorem bestAtPrice_priority (L : PriorityLevel) (h : L.orders.Nonempty) :
    ∀ r ∈ L.orders, r ≠ L.best h → ranksBefore (L.best h) r := by
  intro r hr hne
  have hmax := (Trie.best_true_spec L.wf).2 (priorityKey r.fee r.seq)
    (by rw [L.keys_eq, Finset.mem_image]; exact ⟨r, hr, rfl⟩)
  rw [← L.best_key h] at hmax
  obtain ⟨_, hsr⟩ := L.bounded r hr
  obtain ⟨_, hsb⟩ := L.bounded _ (L.best_mem h)
  rcases Nat.lt_or_eq_of_le hmax with hlt | heq
  · rcases (priorityKey_lt_iff hsr hsb).mp hlt with hf | ⟨hf, hs⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hf.symm, hs⟩
  · exfalso
    obtain ⟨_, hs⟩ := priorityKey_injective hsr hsb heq
    exact hne (L.seq_inj r hr _ (L.best_mem h) hs)

end PriorityLevel

/-! ## A price level in `FIFO` mode -/

/-- `PriceLevel.head/tail` as a queue: `_append` pushes at the tail. -/
def fifoAppend (q : List Resting) (r : Resting) : List Resting := q ++ [r]

/-- Sequences strictly increase along the queue (true of any queue built by `_append` with
    `++nextSequence`, and preserved by `_remove`, which deletes an element). -/
def FifoSorted (q : List Resting) : Prop := q.Pairwise (fun a b => a.seq < b.seq)

theorem fifoAppend_sorted {q : List Resting} {r : Resting} (hq : FifoSorted q)
    (hr : ∀ a ∈ q, a.seq < r.seq) : FifoSorted (fifoAppend q r) := by
  unfold FifoSorted fifoAppend
  rw [List.pairwise_append]
  exact ⟨hq, List.pairwise_singleton _ _, fun a ha b hb => by simp at hb; subst hb; exact hr a ha⟩

theorem fifo_erase_sorted {q : List Resting} (hq : FifoSorted q) (r : Resting) :
    FifoSorted (q.erase r) := hq.sublist List.erase_sublist

/-- **FIFO**: the head of a sorted queue is the earliest resting order. -/
theorem fifo_head_earliest {q : List Resting} (hq : FifoSorted q) (x : Resting) (hx : x ∈ q.tail) :
    ∀ hd, q.head? = some hd → hd.seq < x.seq := by
  intro hd hhd
  cases q with
  | nil => simp at hhd
  | cons a q' =>
    simp only [List.head?_cons, Option.some.injEq] at hhd; subst hhd
    simp only [List.tail_cons] at hx
    exact (List.pairwise_cons.mp hq).1 x hx

/-! ## Sequence assignment -/

/-- `++nextSequence`: a fresh sequence is larger than every sequence handed out before, so a
    repriced order (`updatePrice`: `info.sequence = ++book.nextSequence`) re-enters behind every
    live order, and a new order enters behind every live order. -/
theorem reprice_sequence_last (nextSequence : ℕ) (live : Finset ℕ)
    (hlive : ∀ s ∈ live, s ≤ nextSequence) : ∀ s ∈ live, s < nextSequence + 1 := by
  intro s hs; have := hlive s hs; omega

/-! ## Across levels: the matched level is the best price -/

/-- `book.bids.best(true)` is the highest bid price key present. -/
theorem best_bid_is_max {bids : Trie} (hw : bids.Wf) :
    bids.best true ∈ bids.keys ∧ ∀ p ∈ bids.keys, p ≤ bids.best true :=
  Trie.best_true_spec hw

/-- `book.asks.best(false)` is the lowest ask price key present. -/
theorem best_ask_is_min {asks : Trie} (hw : asks.Wf) :
    asks.best false ∈ asks.keys ∧ ∀ p ∈ asks.keys, asks.best false ≤ p :=
  Trie.best_false_spec hw

/-- `matchIncoming` / `matchBook` only proceed when the best bid reaches the best ask; since
    those are the extrema, if *any* bid reaches *any* ask then the best pair crosses too (the
    book is crossed exactly when the loop would match). -/
theorem crossed_iff_best_crossed {bids asks : Trie} (hb : bids.Wf) (ha : asks.Wf) :
    (∃ p ∈ bids.keys, ∃ q ∈ asks.keys, q ≤ p) ↔ asks.best false ≤ bids.best true := by
  constructor
  · rintro ⟨p, hp, q, hq, hpq⟩
    exact le_trans ((best_ask_is_min ha).2 q hq) (le_trans hpq ((best_bid_is_max hb).2 p hp))
  · intro h
    exact ⟨_, (best_bid_is_max hb).1, _, (best_ask_is_min ha).1, h⟩

end AsyncSwap
