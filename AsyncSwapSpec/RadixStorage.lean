import AsyncSwapSpec.RadixTree

/-!
# RadixPriceTree storage refinement — part 1: model, abstraction, `best`

`RadixTree.lean` proves the Patricia-trie *algorithm* on an inductive tree.  This module
models the contract's *storage* (`struct Tree { root; nextNodeId; freeIds; nodes; leaves }`,
`struct Node { parent; left; right; price; bit; leaf }`) with `insert`, `remove` and `best`
written as `RadixPriceTree.sol` writes them, relates a storage tree to the inductive trie it
encodes (`Reads`), and proves the storage operations refine the verified ones.

Part 1: the model, the representation invariant, frame lemmas, and `best_refines`.
-/

namespace AsyncSwap

structure Node where
  parent : ℕ
  left : ℕ
  right : ℕ
  price : ℕ
  bit : ℕ
  leaf : Bool
  deriving DecidableEq, Repr

def Node.empty : Node := ⟨0, 0, 0, 0, 0, false⟩

/-- `RadixPriceTree.Tree`. Ids are `ℕ`; `0` is the null id as in the contract. -/
structure Tree where
  root : ℕ
  nextNodeId : ℕ
  freeIds : List ℕ
  nodes : ℕ → Node
  leaves : ℕ → ℕ

namespace Tree

def setNode (T : Tree) (id : ℕ) (n : Node) : Tree := { T with nodes := Function.update T.nodes id n }
def setLeaf (T : Tree) (p id : ℕ) : Tree := { T with leaves := Function.update T.leaves p id }

/-- `_newNode`: pop a released id, else `++nextNodeId`. -/
def newNode (T : Tree) : Tree × ℕ :=
  match T.freeIds with
  | id :: rest => ({ T with freeIds := rest }, id)
  | [] => ({ T with nextNodeId := T.nextNodeId + 1 }, T.nextNodeId + 1)

/-- `_freeNode`. -/
def freeNode (T : Tree) (id : ℕ) : Tree :=
  { (T.setNode id Node.empty) with freeIds := id :: T.freeIds }

/-- `best(self, highest)`: walk right (highest) or left (lowest) to a leaf. -/
def bestFrom (T : Tree) (highest : Bool) : ℕ → ℕ → ℕ
  | 0, cursor => (T.nodes cursor).price
  | fuel + 1, cursor =>
      if (T.nodes cursor).leaf then (T.nodes cursor).price
      else bestFrom T highest fuel (if highest then (T.nodes cursor).right else (T.nodes cursor).left)

def best (T : Tree) (highest : Bool) (fuel : ℕ) : Bool × ℕ :=
  if T.root = 0 then (false, 0) else (true, bestFrom T highest fuel T.root)

/-- First `while` of `insert`: descend by the price's bits to a leaf. -/
def descendToLeaf (T : Tree) (price : ℕ) : ℕ → ℕ → ℕ
  | 0, cursor => cursor
  | fuel + 1, cursor =>
      if (T.nodes cursor).leaf then cursor
      else descendToLeaf T price fuel
        (if price.testBit (T.nodes cursor).bit then (T.nodes cursor).right else (T.nodes cursor).left)

/-- Second `while` of `insert`: descend while `bit > splitBit`, remembering the parent.
    Returns `(parentId, cursor)`. -/
def descendUntil (T : Tree) (price split : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, parent, cursor => (parent, cursor)
  | fuel + 1, parent, cursor =>
      if (T.nodes cursor).leaf = false ∧ split < (T.nodes cursor).bit then
        descendUntil T price split fuel cursor
          (if price.testBit (T.nodes cursor).bit then (T.nodes cursor).right else (T.nodes cursor).left)
      else (parent, cursor)

/-- The pointer surgery at the end of `insert`: a fresh branch `branchId` at `split` takes
    `cursor2` and the new leaf `leafId` as children (ordered by the price's bit at `split`), and
    replaces `cursor2` in its parent `parentId`, or in the root slot when `parentId = 0`. -/
def link (T : Tree) (price split leafId branchId parentId cursor2 : ℕ) : Tree :=
  let branch : Node :=
    if price.testBit split then { Node.empty with parent := parentId, bit := split, left := cursor2, right := leafId }
    else { Node.empty with parent := parentId, bit := split, left := leafId, right := cursor2 }
  let T4 := T.setNode branchId branch
  let T5 := T4.setNode cursor2 { T4.nodes cursor2 with parent := branchId }
  let T6 := T5.setNode leafId { T5.nodes leafId with parent := branchId }
  if parentId = 0 then { T6 with root := branchId }
  else if (T6.nodes parentId).left = cursor2 then T6.setNode parentId { T6.nodes parentId with left := branchId }
  else T6.setNode parentId { T6.nodes parentId with right := branchId }

/-- `insert(self, price)` returning `(tree, created)`. -/
def insert (T : Tree) (price : ℕ) (fuel : ℕ) : Tree × Bool :=
  if T.leaves price ≠ 0 then (T, false) else
  let (T1, leafId) := T.newNode
  let T2 := (T1.setNode leafId { Node.empty with price := price, leaf := true }).setLeaf price leafId
  if T2.root = 0 then ({ T2 with root := leafId }, true) else
  let cursor := descendToLeaf T2 price fuel T2.root
  let split := Nat.log2 (price ^^^ (T2.nodes cursor).price)
  let (parentId, cursor2) := descendUntil T2 price split fuel 0 T2.root
  let (T3, branchId) := T2.newNode
  (T3.link price split leafId branchId parentId cursor2, true)

/-- The pointer surgery of `remove` for a non-root leaf: the grandparent (or the root slot)
    now points at the sibling, the sibling's parent becomes the grandparent, and the branch and
    leaf are released. `goLeft` records which child of the grandparent the branch was. -/
def relink (T : Tree) (leafId branchId siblingId grandId : ℕ) (goLeft : Bool) : Tree :=
  let T2 :=
    if grandId = 0 then { T with root := siblingId }
    else if goLeft then T.setNode grandId { T.nodes grandId with left := siblingId }
    else T.setNode grandId { T.nodes grandId with right := siblingId }
  let T3 := T2.setNode siblingId { T2.nodes siblingId with parent := grandId }
  (T3.freeNode branchId).freeNode leafId

/-- `remove(self, price)`; `none` models the `PriceLevelMissing` revert. -/
def remove (T : Tree) (price : ℕ) : Option Tree :=
  let leafId := T.leaves price
  if leafId = 0 then none else
  let T1 := T.setLeaf price 0
  if leafId = T1.root then some { (T1.freeNode leafId) with root := 0 } else
  let branchId := (T1.nodes leafId).parent
  let siblingId := if (T1.nodes branchId).left = leafId then (T1.nodes branchId).right else (T1.nodes branchId).left
  let grandId := (T1.nodes branchId).parent
  some (T1.relink leafId branchId siblingId grandId ((T1.nodes grandId).left = branchId))

end Tree

/-! ## Abstraction -/

/-- Following pointers from node `id` in `T` reads the inductive trie `t`, with consistent
    parent pointers at every child. -/
inductive Reads (T : Tree) : ℕ → Trie → Prop
  | leaf (id p : ℕ) : id ≠ 0 → (T.nodes id).leaf = true → (T.nodes id).price = p →
      Reads T id (Trie.leaf p)
  | branch (id b : ℕ) (l r : Trie) : id ≠ 0 → (T.nodes id).leaf = false → (T.nodes id).bit = b →
      Reads T (T.nodes id).left l → Reads T (T.nodes id).right r →
      (T.nodes (T.nodes id).left).parent = id → (T.nodes (T.nodes id).right).parent = id →
      Reads T id (Trie.branch b l r)

/-- The node ids a read tree occupies, in pre-order. -/
def idsFrom (T : Tree) : ℕ → Trie → List ℕ
  | id, Trie.leaf _ => [id]
  | id, Trie.branch _ l r => id :: (idsFrom T (T.nodes id).left l ++ idsFrom T (T.nodes id).right r)

/-- Representation invariant: `T` stores exactly `t`. -/
structure Repr (T : Tree) (t : Trie) : Prop where
  reads : Reads T T.root t
  nodup : (idsFrom T T.root t).Nodup
  root_parent : (T.nodes T.root).parent = 0
  leaves_mem : ∀ p ∈ t.keys, Reads T (T.leaves p) (Trie.leaf p) ∧ T.leaves p ∈ idsFrom T T.root t
  leaves_absent : ∀ p, p ∉ t.keys → T.leaves p = 0
  ids_fresh : ∀ id ∈ idsFrom T T.root t, id ≤ T.nextNodeId ∧ id ∉ T.freeIds
  free_fresh : ∀ id ∈ T.freeIds, id ≤ T.nextNodeId ∧ id ≠ 0
  free_nodup : T.freeIds.Nodup

/-- Empty storage tree represents "no trie" (`root = 0`). -/
def Tree.empty : Tree := ⟨0, 0, [], fun _ => Node.empty, fun _ => 0⟩

/-! ## Frame lemmas: reading is unaffected by writes outside the read ids -/

theorem Reads.mono {T T' : Tree} {id : ℕ} {t : Trie} (h : Reads T id t)
    (hsame : ∀ x ∈ idsFrom T id t, T'.nodes x = T.nodes x) : Reads T' id t := by
  induction h with
  | leaf id p hne hl hp =>
    have := hsame id (by simp [idsFrom])
    exact Reads.leaf id p hne (by rw [this]; exact hl) (by rw [this]; exact hp)
  | branch id b l r hne hl hb hL hR hpL hpR ihL ihR =>
    have hid := hsame id (by simp [idsFrom])
    have hL' := ihL (fun x hx => hsame x (by simp [idsFrom, hx]))
    have hR' := ihR (fun x hx => hsame x (by simp [idsFrom, hx]))
    have hleftnode : T'.nodes (T.nodes id).left = T.nodes (T.nodes id).left := by
      apply hsame; simp only [idsFrom, List.mem_cons, List.mem_append]; right; left
      cases l <;> simp [idsFrom]
    have hrightnode : T'.nodes (T.nodes id).right = T.nodes (T.nodes id).right := by
      apply hsame; simp only [idsFrom, List.mem_cons, List.mem_append]; right; right
      cases r <;> simp [idsFrom]
    refine Reads.branch id b l r hne (by rw [hid]; exact hl) (by rw [hid]; exact hb) ?_ ?_ ?_ ?_
    · rw [hid]; exact hL'
    · rw [hid]; exact hR'
    · rw [hid, hleftnode]; exact hpL
    · rw [hid, hrightnode]; exact hpR

theorem idsFrom_mono {T T' : Tree} {id : ℕ} {t : Trie} (h : Reads T id t)
    (hsame : ∀ x ∈ idsFrom T id t, T'.nodes x = T.nodes x) : idsFrom T' id t = idsFrom T id t := by
  induction h with
  | leaf id p _ _ _ => rfl
  | branch id b l r _ _ _ hL hR _ _ ihL ihR =>
    have hid := hsame id (by simp [idsFrom])
    simp only [idsFrom, hid]
    rw [ihL (fun x hx => hsame x (by simp [idsFrom, hx])), ihR (fun x hx => hsame x (by simp [idsFrom, hx]))]

theorem Reads.ne_zero {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) : id ≠ 0 := by
  cases h <;> assumption

theorem mem_idsFrom_self (T : Tree) (id : ℕ) (t : Trie) : id ∈ idsFrom T id t := by
  cases t <;> simp [idsFrom]

/-! ## `best` refines -/

theorem bestFrom_refines {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) (highest : Bool) :
    ∀ fuel, t.height ≤ fuel → T.bestFrom highest fuel id = t.best highest := by
  induction h with
  | leaf id p _ hl hp =>
    intro fuel _
    cases fuel <;> simp [Tree.bestFrom, Trie.best, hl, hp]
  | branch id b l r _ hl hb hL hR _ _ ihL ihR =>
    intro fuel hf
    cases fuel with
    | zero => simp [Trie.height] at hf
    | succ fuel =>
      simp only [Tree.bestFrom, hl, Bool.false_eq_true, ↓reduceIte, Trie.best]
      simp only [Trie.height] at hf
      cases highest
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact ihL fuel (by omega)
      · simp only [↓reduceIte]; exact ihR fuel (by omega)

/-- **Storage `best` is the trie's `best`**, hence the exact max / min of the stored prices. -/
theorem best_refines {T : Tree} {t : Trie} (h : Repr T t) (highest : Bool) {fuel : ℕ}
    (hf : t.height ≤ fuel) : T.best highest fuel = (true, t.best highest) := by
  unfold Tree.best
  rw [ite_eq_right h.reads.ne_zero, bestFrom_refines h.reads highest fuel hf]

theorem best_empty (highest : Bool) (fuel : ℕ) : Tree.empty.best highest fuel = (false, 0) := by
  simp [Tree.best, Tree.empty]

end AsyncSwap
