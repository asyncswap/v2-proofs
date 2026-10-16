import AsyncSwapSpec.RadixRemove

/-!
# RadixPriceTree storage refinement — part 3: `insert`

`Tree.insert` (RadixStorage.lean) is the contract's `insert`: allocate a leaf, descend by the
price's bits to the nearest leaf, compute the split bit, descend again while the split is below
the current branch bit, allocate a branch and `link` it in.  This module proves it stores exactly
`Trie.insert` / `PriceIndex.insert` of the represented trie.
-/

namespace AsyncSwap

/-! ## The id allocator -/

/-- The allocator's invariant relative to the ids currently in use. -/
structure Alloc (T : Tree) (used : List ℕ) : Prop where
  used_le : ∀ id ∈ used, id ≤ T.nextNodeId
  used_free : ∀ id ∈ used, id ∉ T.freeIds
  free_le : ∀ id ∈ T.freeIds, id ≤ T.nextNodeId
  free_ne : ∀ id ∈ T.freeIds, id ≠ 0
  free_nodup : T.freeIds.Nodup

theorem Repr.alloc {T : Tree} {t : Trie} (h : Repr T t) : Alloc T (idsFrom T T.root t) :=
  { used_le := fun id hid => (h.ids_fresh id hid).1
    used_free := fun id hid => (h.ids_fresh id hid).2
    free_le := fun id hid => (h.free_fresh id hid).1
    free_ne := fun id hid => (h.free_fresh id hid).2
    free_nodup := h.free_nodup }

/-- `_newNode` hands out an id that is neither `0` nor in use, touches nothing else, and keeps
    the allocator invariant with the new id in use. -/
theorem newNode_spec {T : Tree} {used : List ℕ} (A : Alloc T used) :
    T.newNode.2 ≠ 0 ∧ T.newNode.2 ∉ used ∧ T.newNode.1.nodes = T.nodes ∧ T.newNode.1.root = T.root ∧
    T.newNode.1.leaves = T.leaves ∧ Alloc T.newNode.1 (T.newNode.2 :: used) ∧
    (∀ x ∈ T.newNode.1.freeIds, x ∈ T.freeIds) ∧ T.nextNodeId ≤ T.newNode.1.nextNodeId := by
  rcases hf : T.freeIds with _ | ⟨id, rest⟩
  · simp only [Tree.newNode, hf]
    refine ⟨by omega, fun h => by have := A.used_le _ h; omega, trivial, trivial, trivial, ?_, by simp, by simp⟩
    exact
      { used_le := by
          intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_refl _
          · have := A.used_le x hx; simp; omega
        used_free := by simp
        free_le := by simp
        free_ne := by simp
        free_nodup := by simp }
  · simp only [Tree.newNode, hf]
    have hid : id ∈ T.freeIds := by rw [hf]; exact List.mem_cons_self
    have hnd := A.free_nodup; rw [hf] at hnd
    obtain ⟨hid_rest, hrest⟩ := List.nodup_cons.1 hnd
    refine ⟨A.free_ne id hid, fun h => A.used_free id h hid, trivial, trivial, trivial, ?_,
      fun x hx => List.mem_cons_of_mem _ hx, le_refl _⟩
    exact
      { used_le := by
          intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact A.free_le _ hid
          · exact A.used_le x hx
        used_free := by
          intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hid_rest
          · exact fun hr => A.used_free x hx (by rw [hf]; exact List.mem_cons_of_mem _ hr)
        free_le := fun x hx => A.free_le x (by rw [hf]; exact List.mem_cons_of_mem _ hx)
        free_ne := fun x hx => A.free_ne x (by rw [hf]; exact List.mem_cons_of_mem _ hx)
        free_nodup := hrest }

/-! ## `link` lookups -/

namespace Tree
section Link
variable (T : Tree) (price split leafId branchId parentId cursor2 : ℕ)

theorem link_nodes_other {x : ℕ} (h1 : x ≠ branchId) (h2 : x ≠ cursor2) (h3 : x ≠ leafId) (h4 : x ≠ parentId) :
    (T.link price split leafId branchId parentId cursor2).nodes x = T.nodes x := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1, h2, h3, h4]

theorem link_nodes_branch (h1 : branchId ≠ cursor2) (h2 : branchId ≠ leafId) (h3 : branchId ≠ parentId) :
    (T.link price split leafId branchId parentId cursor2).nodes branchId =
      if price.testBit split then { Node.empty with parent := parentId, bit := split, left := cursor2, right := leafId }
      else { Node.empty with parent := parentId, bit := split, left := leafId, right := cursor2 } := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem link_nodes_cursor (h1 : cursor2 ≠ leafId) (h2 : cursor2 ≠ parentId) (h3 : cursor2 ≠ branchId) :
    (T.link price split leafId branchId parentId cursor2).nodes cursor2 = { T.nodes cursor2 with parent := branchId } := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem link_nodes_leaf (h1 : leafId ≠ parentId) (h2 : leafId ≠ branchId) (h3 : leafId ≠ cursor2) :
    (T.link price split leafId branchId parentId cursor2).nodes leafId = { T.nodes leafId with parent := branchId } := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem link_nodes_parent (h0 : parentId ≠ 0) (h1 : parentId ≠ branchId) (h2 : parentId ≠ cursor2)
    (h3 : parentId ≠ leafId) :
    (T.link price split leafId branchId parentId cursor2).nodes parentId =
      if (T.nodes parentId).left = cursor2 then { T.nodes parentId with left := branchId }
      else { T.nodes parentId with right := branchId } := by
  simp only [link]
  split_ifs <;> simp_all [nodes_setNode, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem link_parent_other {x : ℕ} (h1 : x ≠ branchId) (h2 : x ≠ cursor2) (h3 : x ≠ leafId) :
    ((T.link price split leafId branchId parentId cursor2).nodes x).parent = (T.nodes x).parent := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1, h2, h3] <;> split_ifs <;> simp_all

theorem link_leaf_price {x : ℕ} (h1 : x ≠ branchId) :
    ((T.link price split leafId branchId parentId cursor2).nodes x).leaf = (T.nodes x).leaf ∧
    ((T.link price split leafId branchId parentId cursor2).nodes x).price = (T.nodes x).price := by
  simp only [link]
  split_ifs <;> simp [nodes_setNode, h1] <;> split_ifs <;> simp_all

@[simp] theorem link_root :
    (T.link price split leafId branchId parentId cursor2).root = if parentId = 0 then branchId else T.root := by
  simp only [link]; split_ifs <;> rfl
@[simp] theorem link_leaves : (T.link price split leafId branchId parentId cursor2).leaves = T.leaves := by
  simp only [link]; split_ifs <;> rfl
@[simp] theorem link_freeIds : (T.link price split leafId branchId parentId cursor2).freeIds = T.freeIds := by
  simp only [link]; split_ifs <;> rfl
@[simp] theorem link_nextNodeId :
    (T.link price split leafId branchId parentId cursor2).nextNodeId = T.nextNodeId := by
  simp only [link]; split_ifs <;> rfl

end Link
end Tree

/-! ## The first loop: `descendToLeaf` finds `findLeaf` -/

theorem descendToLeaf_refines {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) (p : ℕ) :
    ∀ fuel, t.height ≤ fuel →
      ∃ x ∈ idsFrom T id t, T.descendToLeaf p fuel id = x ∧ Reads T x (Trie.leaf (t.findLeaf p)) := by
  induction h with
  | leaf id q hne hl hp =>
    intro fuel _
    refine ⟨id, mem_idsFrom_self _ _ _, ?_, Reads.leaf id q hne hl hp⟩
    cases fuel <;> simp [Tree.descendToLeaf, hl]
  | branch id b l r _ hl hb hL hR _ _ ihL ihR =>
    intro fuel hf
    cases fuel with
    | zero => simp [Trie.height] at hf
    | succ fuel =>
      simp only [Tree.descendToLeaf, hl, Bool.false_eq_true, ↓reduceIte, hb, Trie.findLeaf]
      simp only [Trie.height] at hf
      cases hbit : p.testBit b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        obtain ⟨x, hx, he, hr⟩ := ihL fuel (by omega)
        exact ⟨x, by simp [idsFrom, hx], he, hr⟩
      · simp only [↓reduceIte]
        obtain ⟨x, hx, he, hr⟩ := ihR fuel (by omega)
        exact ⟨x, by simp [idsFrom, hx], he, hr⟩

/-! ## The second loop and `link`: the stop -/

section Insert

variable {T : Tree} {p leafId branchId : ℕ}

/-- Global facts about the two fresh ids `insert` allocated. -/
structure InsertCtx (T : Tree) (p leafId branchId : ℕ) : Prop where
  leaf_ne_zero : leafId ≠ 0
  branch_ne_zero : branchId ≠ 0
  leaf_ne_branch : leafId ≠ branchId
  leaf_node : (T.nodes leafId).leaf = true
  leaf_price : (T.nodes leafId).price = p

/-- The trie `insertAt` builds when the descent stops at `t`. -/
def stopTrie (p split : ℕ) (t : Trie) : Trie :=
  if p.testBit split then Trie.branch split t (Trie.leaf p) else Trie.branch split (Trie.leaf p) t

theorem insertAt_leaf (p split q : ℕ) : (Trie.leaf q).insertAt p split = stopTrie p split (Trie.leaf q) := by
  simp only [Trie.insertAt, stopTrie]

theorem insertAt_branch_stop {p split b : ℕ} {l r : Trie} (h : ¬ split < b) :
    (Trie.branch b l r).insertAt p split = stopTrie p split (Trie.branch b l r) := by
  simp only [Trie.insertAt, stopTrie, h, ↓reduceIte]

/-- **Stop.** Linking a fresh branch above the node where the descent stops: the branch reads
    `stopTrie`, the ids are the old ones plus the two fresh ids, and the branch's parent is the
    old node's parent. -/
theorem link_stop (C : InsertCtx T p leafId branchId) (split : ℕ) {id : ℕ} {t : Trie} (h : Reads T id t)
    (hnd : (idsFrom T id t).Nodup) (hleaf : leafId ∉ idsFrom T id t) (hbr : branchId ∉ idsFrom T id t)
    {par : ℕ} (hpar : (T.nodes id).parent = par) (hpar_nin : par ∉ idsFrom T id t)
    (hpl : par ≠ leafId) (hpb : par ≠ branchId) :
    Reads (T.link p split leafId branchId par id) branchId (stopTrie p split t) ∧
    (∀ y ∈ idsFrom (T.link p split leafId branchId par id) branchId (stopTrie p split t),
        y ∈ idsFrom T id t ∨ y = leafId ∨ y = branchId) ∧
    (∀ y ∈ idsFrom T id t, y ∈ idsFrom (T.link p split leafId branchId par id) branchId (stopTrie p split t)) ∧
    leafId ∈ idsFrom (T.link p split leafId branchId par id) branchId (stopTrie p split t) ∧
    branchId ∈ idsFrom (T.link p split leafId branchId par id) branchId (stopTrie p split t) ∧
    (idsFrom (T.link p split leafId branchId par id) branchId (stopTrie p split t)).Nodup ∧
    ((T.link p split leafId branchId par id).nodes branchId).parent = par := by
  have hid_mem := mem_idsFrom_self T id t
  have hid_leaf : id ≠ leafId := fun e => hleaf (mem_idsFrom_of_eq e)
  have hid_br : id ≠ branchId := fun e => hbr (mem_idsFrom_of_eq e)
  have hid_par : id ≠ par := fun e => hpar_nin (mem_idsFrom_of_eq e)
  set T' := T.link p split leafId branchId par id with hT'
  have hbrnode := Tree.link_nodes_branch T p split leafId branchId par id hid_br.symm C.leaf_ne_branch.symm hpb.symm
  have hcur := Tree.link_nodes_cursor T p split leafId branchId par id hid_leaf hid_par hid_br
  have hlf := Tree.link_nodes_leaf T p split leafId branchId par id hpl.symm C.leaf_ne_branch (Ne.symm hid_leaf)
  rw [← hT'] at hbrnode hcur hlf
  have hsame : ∀ y ∈ idsFrom T id t, y ≠ id → T'.nodes y = T.nodes y := by
    intro y hy hyid
    rw [hT']
    exact Tree.link_nodes_other T p split leafId branchId par id (fun e => hbr (by rw [e] at hy; exact hy)) hyid
      (fun e => hleaf (by rw [e] at hy; exact hy)) (fun e => hpar_nin (by rw [e] at hy; exact hy))
  have hreads_id : Reads T' id t :=
    h.mono_root hnd hsame (by rw [hcur]) (by rw [hcur]) (by rw [hcur]) (by rw [hcur]) (by rw [hcur])
  have hids_id : idsFrom T' id t = idsFrom T id t :=
    idsFrom_mono_lr h (fun y hy => by
      by_cases hyid : y = id
      · subst hyid; rw [hcur]; exact ⟨rfl, rfl⟩
      · rw [hsame y hy hyid]; exact ⟨rfl, rfl⟩)
  have hreads_leaf : Reads T' leafId (Trie.leaf p) :=
    Reads.leaf leafId p C.leaf_ne_zero (by rw [hlf]; exact C.leaf_node) (by rw [hlf]; exact C.leaf_price)
  have hpar_id : (T'.nodes id).parent = branchId := by rw [hcur]
  have hpar_leaf : (T'.nodes leafId).parent = branchId := by rw [hlf]
  cases hbit : p.testBit split
  · -- the new leaf is the left child
    simp only [hbit, Bool.false_eq_true, ↓reduceIte] at hbrnode
    have hbl : (T'.nodes branchId).left = leafId := by rw [hbrnode]
    have hbr' : (T'.nodes branchId).right = id := by rw [hbrnode]
    have hbp : (T'.nodes branchId).parent = par := by rw [hbrnode]
    have hreads : Reads T' branchId (stopTrie p split t) := by
      simp only [stopTrie, hbit, Bool.false_eq_true, ↓reduceIte]
      refine Reads.branch branchId split (Trie.leaf p) t C.branch_ne_zero (by rw [hbrnode]; rfl) (by rw [hbrnode]) ?_ ?_ ?_ ?_
      · rw [hbl]; exact hreads_leaf
      · rw [hbr']; exact hreads_id
      · rw [hbl]; exact hpar_leaf
      · rw [hbr']; exact hpar_id
    have hids : idsFrom T' branchId (stopTrie p split t) = branchId :: ([leafId] ++ idsFrom T id t) := by
      simp only [stopTrie, hbit, Bool.false_eq_true, ↓reduceIte, idsFrom, hbl, hbr', hids_id]
    refine ⟨hreads, ?_, ?_, ?_, ?_, ?_, hbp⟩
    · intro y hy; rw [hids] at hy; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | hy
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hy
    · intro y hy; rw [hids]; simp [hy]
    · rw [hids]; simp
    · rw [hids]; simp
    · rw [hids]
      refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨List.nodup_singleton _, hnd, ?_⟩⟩
      · simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨C.leaf_ne_branch.symm, hbr⟩
      · intro a ha c hc e; simp only [List.mem_singleton] at ha; subst ha
        exact hleaf (by rw [e]; exact hc)
  · -- the new leaf is the right child
    simp only [hbit, ↓reduceIte] at hbrnode
    have hbl : (T'.nodes branchId).left = id := by rw [hbrnode]
    have hbr' : (T'.nodes branchId).right = leafId := by rw [hbrnode]
    have hbp : (T'.nodes branchId).parent = par := by rw [hbrnode]
    have hreads : Reads T' branchId (stopTrie p split t) := by
      simp only [stopTrie, hbit, ↓reduceIte]
      refine Reads.branch branchId split t (Trie.leaf p) C.branch_ne_zero (by rw [hbrnode]; rfl) (by rw [hbrnode]) ?_ ?_ ?_ ?_
      · rw [hbl]; exact hreads_id
      · rw [hbr']; exact hreads_leaf
      · rw [hbl]; exact hpar_id
      · rw [hbr']; exact hpar_leaf
    have hids : idsFrom T' branchId (stopTrie p split t) = branchId :: (idsFrom T id t ++ [leafId]) := by
      simp only [stopTrie, hbit, ↓reduceIte, idsFrom, hbl, hbr', hids_id]
    refine ⟨hreads, ?_, ?_, ?_, ?_, ?_, hbp⟩
    · intro y hy; rw [hids] at hy; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | hy | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl hy
      · exact Or.inr (Or.inl rfl)
    · intro y hy; rw [hids]; simp [hy]
    · rw [hids]; simp
    · rw [hids]; simp
    · rw [hids]
      refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hnd, List.nodup_singleton _, ?_⟩⟩
      · simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hbr, C.leaf_ne_branch.symm⟩
      · intro a ha c hc e; simp only [List.mem_singleton] at hc; subst hc
        exact hleaf (by rw [← e]; exact ha)

/-! ## The second loop and `link`: the whole subtree reads `insertAt` -/

/-- **Lemma C.** From any node `id` whose subtree does not contain the fresh ids, the second
    loop finds the stop point `x` with parent `par'`, and `link` makes the subtree read
    `t.insertAt p split` (rooted at the fresh branch when the stop is `id` itself). The ids are
    the old ones plus the two fresh ids, still `Nodup`, and the subtree's parent is unchanged. -/
theorem reads_inserted (C : InsertCtx T p leafId branchId) (split : ℕ) :
    ∀ {id : ℕ} {t : Trie}, Reads T id t → (idsFrom T id t).Nodup →
      leafId ∉ idsFrom T id t → branchId ∉ idsFrom T id t →
      ∀ fuel, t.height ≤ fuel → ∀ par, (T.nodes id).parent = par → par ∉ idsFrom T id t →
        par ≠ leafId → par ≠ branchId →
      ∀ par' x, T.descendUntil p split fuel par id = (par', x) →
      x ∈ idsFrom T id t ∧ (par' = par ↔ x = id) ∧ (x ≠ id → par' ∈ idsFrom T id t) ∧
      Reads (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split) ∧
      (∀ y ∈ idsFrom (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split),
          y ∈ idsFrom T id t ∨ y = leafId ∨ y = branchId) ∧
      (∀ y ∈ idsFrom T id t,
          y ∈ idsFrom (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split)) ∧
      leafId ∈ idsFrom (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split) ∧
      branchId ∈ idsFrom (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split) ∧
      (idsFrom (T.link p split leafId branchId par' x) (if x = id then branchId else id) (t.insertAt p split)).Nodup ∧
      ((T.link p split leafId branchId par' x).nodes (if x = id then branchId else id)).parent = par := by
  intro id t h
  induction h with
  | leaf id q hne hl hq =>
    intro hnd hleaf hbr fuel _ par hpar hpar_nin hpl hpb par' x hdesc
    have hx : par = par' ∧ id = x := by
      cases fuel <;> simpa [Tree.descendUntil, hl] using hdesc
    obtain ⟨rfl, rfl⟩ := hx
    simp only [eq_self_iff_true, ↓reduceIte, insertAt_leaf]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
      link_stop C split (Reads.leaf id q hne hl hq) hnd hleaf hbr hpar hpar_nin hpl hpb
    exact ⟨mem_idsFrom_self _ _ _, by simp, fun h => absurd rfl h, h1, h2, h3, h4, h5, h6, h7⟩
  | branch id b l r hne hl hb hL hR hpL hpR ihL ihR =>
    intro hnd hleaf hbr fuel hf par hpar hpar_nin hpl hpb par' x hdesc
    have hnd' := hnd
    simp only [idsFrom, List.nodup_cons, List.nodup_append, List.mem_append, not_or] at hnd'
    obtain ⟨⟨hid_l, hid_r⟩, hndL, hndR, hdisj⟩ := hnd'
    have hleaf' : ¬ leafId = id ∧ leafId ∉ idsFrom T (T.nodes id).left l ∧ leafId ∉ idsFrom T (T.nodes id).right r := by
      simpa only [idsFrom, List.mem_cons, List.mem_append, not_or] using hleaf
    have hbr' : ¬ branchId = id ∧ branchId ∉ idsFrom T (T.nodes id).left l ∧ branchId ∉ idsFrom T (T.nodes id).right r := by
      simpa only [idsFrom, List.mem_cons, List.mem_append, not_or] using hbr
    have hpar' : ¬ par = id ∧ par ∉ idsFrom T (T.nodes id).left l ∧ par ∉ idsFrom T (T.nodes id).right r := by
      simpa only [idsFrom, List.mem_cons, List.mem_append, not_or] using hpar_nin
    obtain ⟨hleaf_id, hleaf_l, hleaf_r⟩ := hleaf'
    obtain ⟨hbr_id, hbr_l, hbr_r⟩ := hbr'
    obtain ⟨hpar_id, hpar_l, hpar_r⟩ := hpar'
    have hreads : Reads T id (Trie.branch b l r) := Reads.branch id b l r hne hl hb hL hR hpL hpR
    cases fuel with
    | zero => simp [Trie.height] at hf
    | succ fuel =>
    simp only [Trie.height] at hf
    by_cases hsplit : split < b
    · -- the descent continues into the child selected by the price's bit `b`
      simp only [Tree.descendUntil, hl, hb, hsplit, eq_self_iff_true, true_and, and_self, ↓reduceIte] at hdesc
      cases hbit : p.testBit b
      · -- into the left child
        simp only [hbit, Bool.false_eq_true, ↓reduceIte] at hdesc
        obtain ⟨hx, hiff, hpar'_mem, hRl, hsub, hsup, hlm, hbm, hndl, hpp⟩ :=
          ihL hndL hleaf_l hbr_l fuel (by omega) id hpL hid_l (Ne.symm hleaf_id) (Ne.symm hbr_id) par' x hdesc
        have hx_id : x ≠ id := fun e => hid_l (by rw [e] at hx; exact hx)
        have hx_leaf : x ≠ leafId := fun e => hleaf_l (by rw [e] at hx; exact hx)
        have hx_br : x ≠ branchId := fun e => hbr_l (by rw [e] at hx; exact hx)
        have hx_r : x ∉ idsFrom T (T.nodes id).right r := fun hr => hdisj x hx x hr rfl
        have hpar'_ne_par : par' ≠ par := by
          intro e
          by_cases hxl : x = (T.nodes id).left
          · exact hpar_id (by rw [← e]; exact hiff.2 hxl)
          · exact hpar_l (by rw [← e]; exact hpar'_mem hxl)
        have hpar'_ne_r : ∀ y ∈ idsFrom T (T.nodes id).right r, y ≠ par' := by
          intro y hy e
          by_cases hxl : x = (T.nodes id).left
          · rw [hiff.2 hxl] at e; exact hid_r (by rw [e] at hy; exact hy)
          · exact hdisj _ (hpar'_mem hxl) _ hy e.symm
        set T' := T.link p split leafId branchId par' x with hT'
        have hnode : (T'.nodes id).left = (if x = (T.nodes id).left then branchId else (T.nodes id).left) ∧
            (T'.nodes id).right = (T.nodes id).right ∧ (T'.nodes id).leaf = (T.nodes id).leaf ∧
            (T'.nodes id).bit = (T.nodes id).bit ∧ (T'.nodes id).parent = (T.nodes id).parent := by
          by_cases hxl : x = (T.nodes id).left
          · have hpid : par' = id := hiff.2 hxl
            rw [hT', hpid, Tree.link_nodes_parent T p split leafId branchId id x hne (Ne.symm hbr_id) (Ne.symm hx_id)
              (Ne.symm hleaf_id)]
            simp only [← hxl, eq_self_iff_true, ↓reduceIte]
            exact ⟨trivial, trivial, trivial, trivial, trivial⟩
          · have hpid : par' ≠ id := fun e => hxl (hiff.1 e)
            rw [hT', Tree.link_nodes_other T p split leafId branchId par' x (Ne.symm hbr_id) (Ne.symm hx_id)
              (Ne.symm hleaf_id) (Ne.symm hpid)]
            simp only [hxl, ↓reduceIte]
            exact ⟨trivial, trivial, trivial, trivial, trivial⟩
        obtain ⟨hnl, hnr, hnleaf, hnbit, hnpar⟩ := hnode
        have hsameR : ∀ y ∈ idsFrom T (T.nodes id).right r, T'.nodes y = T.nodes y := by
          intro y hy
          rw [hT']
          exact Tree.link_nodes_other T p split leafId branchId par' x (fun e => hbr_r (by rw [e] at hy; exact hy))
            (fun e => hx_r (by rw [e] at hy; exact hy)) (fun e => hleaf_r (by rw [e] at hy; exact hy)) (hpar'_ne_r y hy)
        have hRr : Reads T' (T.nodes id).right r := hR.mono hsameR
        have hRids : idsFrom T' (T.nodes id).right r = idsFrom T (T.nodes id).right r := idsFrom_mono hR hsameR
        simp only [hx_id, ↓reduceIte, Trie.insertAt, hsplit, hbit, Bool.false_eq_true]
        have hids' : idsFrom T' id (Trie.branch b (l.insertAt p split) r) =
            id :: (idsFrom T' (if x = (T.nodes id).left then branchId else (T.nodes id).left) (l.insertAt p split) ++
              idsFrom T (T.nodes id).right r) := by
          simp only [idsFrom, hnl, hnr, hRids]
        refine ⟨by simp [idsFrom, hx], ⟨fun e => absurd e hpar'_ne_par, fun e => e.elim⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _
          by_cases hxl : x = (T.nodes id).left
          · rw [hiff.2 hxl]; exact mem_idsFrom_self _ _ _
          · simp only [idsFrom, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl (hpar'_mem hxl))
        · refine Reads.branch id b (l.insertAt p split) r hne (by rw [hnleaf]; exact hl) (by rw [hnbit]; exact hb) ?_ ?_ ?_ ?_
          · rw [hnl]; exact hRl
          · rw [hnr]; exact hRr
          · rw [hnl]; exact hpp
          · rw [hnr, hT', Tree.link_parent_other T p split leafId branchId par' x (fun e => hbr_r (mem_idsFrom_of_eq e))
              (fun e => hx_r (mem_idsFrom_of_eq e)) (fun e => hleaf_r (mem_idsFrom_of_eq e))]
            exact hpR
        · intro y hy; rw [hids'] at hy; simp only [List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | hy | hy
          · exact Or.inl (mem_idsFrom_self _ _ _)
          · rcases hsub y hy with h1 | h1 | h1
            · exact Or.inl (by simp [idsFrom, h1])
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr h1)
          · exact Or.inl (by simp [idsFrom, hy])
        · intro y hy; rw [hids']; simp only [idsFrom, List.mem_cons, List.mem_append] at hy ⊢
          rcases hy with rfl | hy | hy
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (hsup y hy))
          · exact Or.inr (Or.inr hy)
        · rw [hids']; simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hlm)
        · rw [hids']; simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hbm)
        · rw [hids']
          refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hndl, hndR, ?_⟩⟩
          · simp only [List.mem_append, not_or]
            refine ⟨fun hy => ?_, hid_r⟩
            rcases hsub id hy with h1 | h1 | h1
            · exact hid_l h1
            · exact hleaf_id h1.symm
            · exact hbr_id h1.symm
          · intro a ha c hc e
            rcases hsub a ha with h1 | h1 | h1
            · exact hdisj a h1 c hc e
            · rw [← e, h1] at hc; exact hleaf_r hc
            · rw [← e, h1] at hc; exact hbr_r hc
        · rw [hnpar]; exact hpar
      · -- into the right child
        simp only [hbit, ↓reduceIte] at hdesc
        obtain ⟨hx, hiff, hpar'_mem, hRr, hsub, hsup, hlm, hbm, hndr, hpp⟩ :=
          ihR hndR hleaf_r hbr_r fuel (by omega) id hpR hid_r (Ne.symm hleaf_id) (Ne.symm hbr_id) par' x hdesc
        have hx_id : x ≠ id := fun e => hid_r (by rw [e] at hx; exact hx)
        have hx_leaf : x ≠ leafId := fun e => hleaf_r (by rw [e] at hx; exact hx)
        have hx_br : x ≠ branchId := fun e => hbr_r (by rw [e] at hx; exact hx)
        have hx_l : x ∉ idsFrom T (T.nodes id).left l := fun hl' => hdisj x hl' x hx rfl
        have hlx : (T.nodes id).left ≠ x := hdisj _ (mem_idsFrom_self _ _ _) x hx
        have hpar'_ne_par : par' ≠ par := by
          intro e
          by_cases hxr : x = (T.nodes id).right
          · exact hpar_id (by rw [← e]; exact hiff.2 hxr)
          · exact hpar_r (by rw [← e]; exact hpar'_mem hxr)
        have hpar'_ne_l : ∀ y ∈ idsFrom T (T.nodes id).left l, y ≠ par' := by
          intro y hy e
          by_cases hxr : x = (T.nodes id).right
          · rw [hiff.2 hxr] at e; exact hid_l (by rw [e] at hy; exact hy)
          · exact hdisj _ hy _ (hpar'_mem hxr) e
        set T' := T.link p split leafId branchId par' x with hT'
        have hnode : (T'.nodes id).left = (T.nodes id).left ∧
            (T'.nodes id).right = (if x = (T.nodes id).right then branchId else (T.nodes id).right) ∧
            (T'.nodes id).leaf = (T.nodes id).leaf ∧
            (T'.nodes id).bit = (T.nodes id).bit ∧ (T'.nodes id).parent = (T.nodes id).parent := by
          by_cases hxr : x = (T.nodes id).right
          · have hpid : par' = id := hiff.2 hxr
            rw [hT', hpid, Tree.link_nodes_parent T p split leafId branchId id x hne (Ne.symm hbr_id) (Ne.symm hx_id)
              (Ne.symm hleaf_id)]
            simp only [hlx, ↓reduceIte, ← hxr, eq_self_iff_true]
            exact ⟨trivial, trivial, trivial, trivial, trivial⟩
          · have hpid : par' ≠ id := fun e => hxr (hiff.1 e)
            rw [hT', Tree.link_nodes_other T p split leafId branchId par' x (Ne.symm hbr_id) (Ne.symm hx_id)
              (Ne.symm hleaf_id) (Ne.symm hpid)]
            simp only [hxr, ↓reduceIte]
            exact ⟨trivial, trivial, trivial, trivial, trivial⟩
        obtain ⟨hnl, hnr, hnleaf, hnbit, hnpar⟩ := hnode
        have hsameL : ∀ y ∈ idsFrom T (T.nodes id).left l, T'.nodes y = T.nodes y := by
          intro y hy
          rw [hT']
          exact Tree.link_nodes_other T p split leafId branchId par' x (fun e => hbr_l (by rw [e] at hy; exact hy))
            (fun e => hx_l (by rw [e] at hy; exact hy)) (fun e => hleaf_l (by rw [e] at hy; exact hy)) (hpar'_ne_l y hy)
        have hLl : Reads T' (T.nodes id).left l := hL.mono hsameL
        have hLids : idsFrom T' (T.nodes id).left l = idsFrom T (T.nodes id).left l := idsFrom_mono hL hsameL
        simp only [hx_id, ↓reduceIte, Trie.insertAt, hsplit, hbit]
        have hids' : idsFrom T' id (Trie.branch b l (r.insertAt p split)) =
            id :: (idsFrom T (T.nodes id).left l ++
              idsFrom T' (if x = (T.nodes id).right then branchId else (T.nodes id).right) (r.insertAt p split)) := by
          simp only [idsFrom, hnl, hnr, hLids]
        refine ⟨by simp [idsFrom, hx], ⟨fun e => absurd e hpar'_ne_par, fun e => e.elim⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _
          by_cases hxr : x = (T.nodes id).right
          · rw [hiff.2 hxr]; exact mem_idsFrom_self _ _ _
          · simp only [idsFrom, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr (hpar'_mem hxr))
        · refine Reads.branch id b l (r.insertAt p split) hne (by rw [hnleaf]; exact hl) (by rw [hnbit]; exact hb) ?_ ?_ ?_ ?_
          · rw [hnl]; exact hLl
          · rw [hnr]; exact hRr
          · rw [hnl, hT', Tree.link_parent_other T p split leafId branchId par' x (fun e => hbr_l (mem_idsFrom_of_eq e))
              (fun e => hx_l (mem_idsFrom_of_eq e)) (fun e => hleaf_l (mem_idsFrom_of_eq e))]
            exact hpL
          · rw [hnr]; exact hpp
        · intro y hy; rw [hids'] at hy; simp only [List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | hy | hy
          · exact Or.inl (mem_idsFrom_self _ _ _)
          · exact Or.inl (by simp [idsFrom, hy])
          · rcases hsub y hy with h1 | h1 | h1
            · exact Or.inl (by simp [idsFrom, h1])
            · exact Or.inr (Or.inl h1)
            · exact Or.inr (Or.inr h1)
        · intro y hy; rw [hids']; simp only [idsFrom, List.mem_cons, List.mem_append] at hy ⊢
          rcases hy with rfl | hy | hy
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr (hsup y hy))
        · rw [hids']; simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hlm)
        · rw [hids']; simp only [List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hbm)
        · rw [hids']
          refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hndL, hndr, ?_⟩⟩
          · simp only [List.mem_append, not_or]
            refine ⟨hid_l, fun hy => ?_⟩
            rcases hsub id hy with h1 | h1 | h1
            · exact hid_r h1
            · exact hleaf_id h1.symm
            · exact hbr_id h1.symm
          · intro a ha c hc e
            rcases hsub c hc with h1 | h1 | h1
            · exact hdisj a ha c h1 e
            · rw [e, h1] at ha; exact hleaf_l ha
            · rw [e, h1] at ha; exact hbr_l ha
        · rw [hnpar]; exact hpar
    · -- the descent stops here: a fresh branch goes above `id`
      simp only [Tree.descendUntil, hl, hb, hsplit, eq_self_iff_true, true_and, and_false, ↓reduceIte,
        Prod.mk.injEq] at hdesc
      obtain ⟨rfl, rfl⟩ := hdesc
      simp only [eq_self_iff_true, ↓reduceIte, insertAt_branch_stop hsplit]
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := link_stop C split hreads hnd hleaf hbr hpar hpar_nin hpl hpb
      exact ⟨mem_idsFrom_self _ _ _, by simp, fun h => absurd rfl h, h1, h2, h3, h4, h5, h6, h7⟩

end Insert

/-! ## Top level: `Tree.insert` refines `Trie.insert` / `PriceIndex.insert` -/

theorem Tree.descendUntil_congr {T T' : Tree} (h : T'.nodes = T.nodes) (p split : ℕ) :
    ∀ fuel par id, T'.descendUntil p split fuel par id = T.descendUntil p split fuel par id := by
  intro fuel
  induction fuel with
  | zero => intro par id; rfl
  | succ fuel ih => intro par id; simp only [Tree.descendUntil, h, ih]

section TopLevel

variable {T : Tree} {t : Trie} {p : ℕ}

/-- A present price: `insert` is a no-op reporting `created = false`. -/
theorem insert_present (h : Repr T t) (hp : p ∈ t.keys) (fuel : ℕ) : T.insert p fuel = (T, false) := by
  have : T.leaves p ≠ 0 := (h.leaves_mem p hp).1.ne_zero
  simp [Tree.insert, this]

/-- **Insertion refinement.** A fresh price on a represented trie: `insert` reports
    `created = true` and stores exactly `Trie.insert`. -/
theorem insert_refines (h : Repr T t) (hp : p ∉ t.keys) {fuel : ℕ} (hf : t.height ≤ fuel) :
    (T.insert p fuel).2 = true ∧ Repr (T.insert p fuel).1 (t.insert p) := by
  have hl0 : T.leaves p = 0 := h.leaves_absent p hp
  have hroot0 : T.root ≠ 0 := h.reads.ne_zero
  have hins : t.insert p = t.insertAt p (splitBit p (t.findLeaf p)) := by simp [Trie.insert, hp]
  simp only [Tree.insert, hl0, ne_eq, not_true_eq_false, ↓reduceIte]
  -- the leaf allocation
  rcases hnew1 : T.newNode with ⟨T1, leafId⟩
  have hspec := newNode_spec h.alloc
  rw [hnew1] at hspec; dsimp only at hspec
  obtain ⟨hlne, hlnin, hn1, hr1, hlv1, A1, -, -⟩ := hspec
  dsimp only
  set T2 := (T1.setNode leafId { Node.empty with price := p, leaf := true }).setLeaf p leafId with hT2
  have hT2n : T2.nodes = Function.update T.nodes leafId { Node.empty with price := p, leaf := true } := by
    show Function.update T1.nodes leafId _ = _; rw [hn1]
  have hT2r : T2.root = T.root := hr1
  have hT2l : T2.leaves = Function.update T.leaves p leafId := by
    show Function.update T1.leaves p leafId = _; rw [hlv1]
  have hsame2 : ∀ y ∈ idsFrom T T.root t, T2.nodes y = T.nodes y := by
    intro y hy; rw [hT2n, Function.update_of_ne (fun e => hlnin (by rw [e] at hy; exact hy))]
  have hreads2 : Reads T2 T.root t := h.reads.mono hsame2
  have hleafnode : T2.nodes leafId = { Node.empty with price := p, leaf := true } := by rw [hT2n]; simp
  have A2 : Alloc T2 (leafId :: idsFrom T T.root t) :=
    ⟨A1.used_le, A1.used_free, A1.free_le, A1.free_ne, A1.free_nodup⟩
  simp only [hT2r, hroot0, ↓reduceIte]
  -- the first loop
  obtain ⟨c, hc_mem, hc_eq, hc_reads⟩ := descendToLeaf_refines hreads2 p fuel hf
  rw [hc_eq, hc_reads.leaf_fields.2]
  set split := Nat.log2 (p ^^^ t.findLeaf p) with hsplit
  -- the second loop and the branch allocation
  rcases hdesc : T2.descendUntil p split fuel 0 T.root with ⟨parentId, cursor2⟩
  rcases hnew2 : T2.newNode with ⟨T3, branchId⟩
  have hspec := newNode_spec A2
  rw [hnew2] at hspec; dsimp only at hspec
  obtain ⟨hbne, hbnin, hn3, hr3, hlv3, A3, -, -⟩ := hspec
  simp only [List.mem_cons, not_or] at hbnin
  obtain ⟨hbl, hbnin⟩ := hbnin
  dsimp only
  refine ⟨trivial, ?_⟩
  rw [hins]
  -- Lemma C at the root
  have C : InsertCtx T3 p leafId branchId :=
    { leaf_ne_zero := hlne, branch_ne_zero := hbne, leaf_ne_branch := Ne.symm hbl
      leaf_node := by rw [hn3, hleafnode], leaf_price := by rw [hn3, hleafnode] }
  have hreads3 : Reads T3 T.root t := hreads2.of_nodes_eq hn3
  have hids3 : idsFrom T3 T.root t = idsFrom T T.root t := by
    rw [idsFrom_of_nodes_eq hn3, idsFrom_mono h.reads hsame2]
  have hdesc3 : T3.descendUntil p split fuel 0 T.root = (parentId, cursor2) := by
    rw [Tree.descendUntil_congr hn3]; exact hdesc
  have h0nin : (0 : ℕ) ∉ idsFrom T T.root t := fun h0 => h.reads.ids_ne_zero 0 h0 rfl
  obtain ⟨hx, hiff, hpm, hreads', hsub, hsup, hlm, hbm, hnd', hpp⟩ :=
    reads_inserted C split hreads3 (hids3 ▸ h.nodup) (hids3 ▸ hlnin) (hids3 ▸ hbnin) fuel hf 0
      (by rw [hn3, hsame2 _ (mem_idsFrom_self _ _ _)]; exact h.root_parent) (hids3 ▸ h0nin)
      (Ne.symm hlne) (Ne.symm hbne) parentId cursor2 hdesc3
  rw [hids3] at hx hpm hsub hsup
  set L := T3.link p split leafId branchId parentId cursor2 with hL
  have hLroot : L.root = (if cursor2 = T.root then branchId else T.root) := by
    rw [hL, Tree.link_root, hr3, hT2r]
    by_cases hc : cursor2 = T.root
    · simp only [hc, eq_self_iff_true, ↓reduceIte, hiff.2 hc]
    · have : ¬ parentId = 0 := fun e => hc (hiff.1 e)
      simp only [hc, this, ↓reduceIte]
  have hLn : ∀ y, y ≠ branchId → (L.nodes y).leaf = (T3.nodes y).leaf ∧ (L.nodes y).price = (T3.nodes y).price :=
    fun y hy => by rw [hL]; exact Tree.link_leaf_price T3 p split leafId branchId parentId cursor2 hy
  have hLl : L.leaves = Function.update T.leaves p leafId := by rw [hL, Tree.link_leaves, hlv3, hT2l]
  have hLf : L.freeIds = T3.freeIds := by rw [hL, Tree.link_freeIds]
  have hLx : L.nextNodeId = T3.nextNodeId := by rw [hL, Tree.link_nextNodeId]
  refine
    { reads := ?_, nodup := ?_, root_parent := ?_, leaves_mem := ?_, leaves_absent := ?_,
      ids_fresh := ?_, free_fresh := ?_, free_nodup := ?_ }
  · rw [hLroot]; exact hreads'
  · rw [hLroot]; exact hnd'
  · rw [hLroot]; exact hpp
  · intro q hq
    rw [hLroot, hLl]
    rcases (Trie.mem_keys_insertAt p split q t).1 hq with hqt | rfl
    · have hqp : q ≠ p := fun e => hp (e ▸ hqt)
      rw [Function.update_of_ne hqp]
      obtain ⟨hyr, hym⟩ := h.leaves_mem q hqt
      have hy_br : T.leaves q ≠ branchId := fun e => hbnin (by rw [e] at hym; exact hym)
      have hy_leaf : T.leaves q ≠ leafId := fun e => hlnin (by rw [e] at hym; exact hym)
      obtain ⟨e1, e2⟩ := hLn _ hy_br
      rw [hn3, hsame2 _ hym] at e1 e2
      refine ⟨Reads.leaf _ q hyr.ne_zero (by rw [e1]; exact hyr.leaf_fields.1) (by rw [e2]; exact hyr.leaf_fields.2),
        hsup _ hym⟩
    · rw [Function.update_self]
      obtain ⟨e1, e2⟩ := hLn leafId (Ne.symm hbl)
      rw [hn3, hleafnode] at e1 e2
      exact ⟨Reads.leaf leafId q hlne (by rw [e1]) (by rw [e2]), hlm⟩
  · intro q hq
    rw [hLl]
    have hqp : q ≠ p := fun e => hq ((Trie.mem_keys_insertAt p split q t).2 (Or.inr e))
    rw [Function.update_of_ne hqp]
    exact h.leaves_absent q (fun hqt => hq ((Trie.mem_keys_insertAt p split q t).2 (Or.inl hqt)))
  · intro id hid
    rw [hLroot] at hid
    rw [hLx, hLf]
    have : id ∈ branchId :: leafId :: idsFrom T T.root t := by
      simp only [List.mem_cons]
      rcases hsub id hid with h1 | h1 | h1
      · exact Or.inr (Or.inr h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h1
    exact ⟨A3.used_le id this, A3.used_free id this⟩
  · intro id hid
    rw [hLf] at hid; rw [hLx]
    exact ⟨A3.free_le id hid, A3.free_ne id hid⟩
  · rw [hLf]; exact A3.free_nodup

/-- Inserting into the empty storage: the new leaf becomes the root. -/
theorem insert_empty (h : ReprIx T none) (p fuel : ℕ) :
    (T.insert p fuel).2 = true ∧ Repr (T.insert p fuel).1 (Trie.leaf p) := by
  obtain ⟨hroot, hleaves, hfree, hnodup⟩ := h
  have A : Alloc T [] :=
    ⟨by simp, by simp, fun id hid => (hfree id hid).1, fun id hid => (hfree id hid).2, hnodup⟩
  simp only [Tree.insert, hleaves p, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases hnew1 : T.newNode with ⟨T1, leafId⟩
  have hspec := newNode_spec A
  rw [hnew1] at hspec; dsimp only at hspec
  obtain ⟨hlne, -, hn1, hr1, hlv1, A1, -, -⟩ := hspec
  dsimp only
  set T2 := (T1.setNode leafId { Node.empty with price := p, leaf := true }).setLeaf p leafId with hT2
  have hT2r : T2.root = 0 := by rw [← hroot]; exact hr1
  have hT2n : T2.nodes leafId = { Node.empty with price := p, leaf := true } := by
    show Function.update T1.nodes leafId _ leafId = _; simp
  have hT2l : T2.leaves = Function.update T.leaves p leafId := by
    show Function.update T1.leaves p leafId = _; rw [hlv1]
  simp only [hT2r, ↓reduceIte]
  refine ⟨trivial, ?_⟩
  refine
    { reads := ?_, nodup := ?_, root_parent := ?_, leaves_mem := ?_, leaves_absent := ?_,
      ids_fresh := ?_, free_fresh := ?_, free_nodup := ?_ }
  · exact Reads.leaf leafId p hlne (by show (T2.nodes leafId).leaf = true; rw [hT2n])
      (by show (T2.nodes leafId).price = p; rw [hT2n])
  · show (idsFrom _ leafId (Trie.leaf p)).Nodup; simp [idsFrom]
  · show (T2.nodes leafId).parent = 0; rw [hT2n]; rfl
  · intro q hq
    simp only [Trie.keys, Finset.mem_singleton] at hq; subst hq
    show Reads _ (T2.leaves q) (Trie.leaf q) ∧ T2.leaves q ∈ idsFrom _ leafId (Trie.leaf q)
    rw [hT2l, Function.update_self]
    exact ⟨Reads.leaf leafId q hlne (by show (T2.nodes leafId).leaf = true; rw [hT2n])
      (by show (T2.nodes leafId).price = q; rw [hT2n]), by simp [idsFrom]⟩
  · intro q hq
    simp only [Trie.keys, Finset.mem_singleton] at hq
    show T2.leaves q = 0
    rw [hT2l, Function.update_of_ne hq]; exact hleaves q
  · intro id hid
    simp only [idsFrom, List.mem_singleton] at hid; subst hid
    exact ⟨A1.used_le _ (by simp), A1.used_free _ (by simp)⟩
  · intro id hid
    exact ⟨A1.free_le id hid, A1.free_ne id hid⟩
  · exact A1.free_nodup

end TopLevel

/-- Height of an optional trie, the fuel `Tree.insert` needs. -/
def PriceIndex.height : PriceIndex → ℕ
  | none => 0
  | some t => t.height

/-- **`PriceIndex.insert` refinement.** On any represented index, the contract's `insert` reports
    `created` exactly when the price was absent and stores exactly `PriceIndex.insert`. -/
theorem PriceIndex.insert_refines {T : Tree} {ix : PriceIndex} (h : ReprIx T ix) {p fuel : ℕ}
    (hf : ix.height ≤ fuel) :
    (T.insert p fuel).2 = decide (p ∉ ix.keys) ∧ ReprIx (T.insert p fuel).1 (ix.insert p) := by
  cases ix with
  | none =>
    obtain ⟨h1, h2⟩ := AsyncSwap.insert_empty h p fuel
    exact ⟨by rw [h1]; simp [PriceIndex.keys], h2⟩
  | some t =>
    by_cases hp : p ∈ t.keys
    · rw [AsyncSwap.insert_present h hp fuel]
      refine ⟨by simp [PriceIndex.keys, hp], ?_⟩
      show Repr T (t.insert p)
      rw [show t.insert p = t by simp [Trie.insert, hp]]; exact h
    · obtain ⟨h1, h2⟩ := AsyncSwap.insert_refines h hp hf
      exact ⟨by rw [h1]; simp [PriceIndex.keys, hp], h2⟩

end AsyncSwap
