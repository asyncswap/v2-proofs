import AsyncSwapSpec.RadixStorage

/-!
# RadixPriceTree storage refinement — part 2: `remove`

`Trie.removeLeaf` deletes the unique leaf holding `p` by identity; on a well-formed trie it
equals the bit-descent `Trie.remove`.  `remove_refines`: under the representation invariant,
the storage `remove` reads exactly `removeLeaf` and re-establishes the invariant.
-/

namespace AsyncSwap

/-! ## Leaf-identity removal on the inductive trie -/

namespace Trie

def removeLeaf (p : ℕ) : Trie → Option Trie
  | leaf q => if q = p then none else some (leaf q)
  | branch b l r =>
      if p ∈ l.keys then
        match l.removeLeaf p with
        | none => some r
        | some l' => some (branch b l' r)
      else
        match r.removeLeaf p with
        | none => some l
        | some r' => some (branch b l r')

theorem remove_eq_removeLeaf {t : Trie} (hw : Wf t) (p : ℕ) (hp : p ∈ t.keys) :
    t.remove p = t.removeLeaf p := by
  induction hw with
  | leaf q => simp [remove, removeLeaf]
  | @branch b l r hl hr h1 h2 _ ihl ihr =>
    simp only [remove, removeLeaf]
    simp only [keys, Finset.mem_union] at hp
    by_cases hpl : p ∈ l.keys
    · have hbit : p.testBit b = false := h1 p hpl
      simp only [hbit, Bool.false_eq_true, ↓reduceIte, hpl]
      rw [ihl hpl]; cases l.removeLeaf p <;> rfl
    · have hpr : p ∈ r.keys := by tauto
      have hbit : p.testBit b = true := h2 p hpr
      simp only [hbit, ↓reduceIte, hpl]
      rw [ihr hpr]; cases r.removeLeaf p <;> rfl

/-- In a well-formed trie a key sits on exactly one side of every branch. -/
theorem Wf.not_both {b : ℕ} {l r : Trie} (hw : Wf (Trie.branch b l r)) {q : ℕ} (hl : q ∈ l.keys) (hr : q ∈ r.keys) : False := by
  cases hw with
  | branch _ _ h1 h2 _ =>
    have := h1 q hl; have := h2 q hr; simp_all

end Trie

/-! ## Structural lemmas about `Reads` -/

theorem Reads.unique {T : Tree} {id : ℕ} {t t' : Trie} (h : Reads T id t) (h' : Reads T id t') : t = t' := by
  induction h generalizing t' with
  | leaf id p _ hl hp =>
    cases h' with
    | leaf _ _ _ _ hp' => rw [← hp, ← hp']
    | branch _ _ _ _ _ hl' => rw [hl] at hl'; exact absurd hl' (by simp)
  | branch id b l r _ hl hb hL hR _ _ ihL ihR =>
    cases h' with
    | leaf _ _ _ hl' => rw [hl] at hl'; exact absurd hl' (by simp)
    | branch _ _ _ _ _ _ hb' hL' hR' => rw [← hb, ← hb', ihL hL', ihR hR']

theorem Reads.sub {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) {x : ℕ} (hx : x ∈ idsFrom T id t) :
    ∃ u, Reads T x u ∧ (∀ y ∈ idsFrom T x u, y ∈ idsFrom T id t) ∧ u.keys ⊆ t.keys := by
  induction h with
  | leaf id p hne hl hp =>
    simp only [idsFrom, List.mem_singleton] at hx; subst hx
    exact ⟨Trie.leaf p, Reads.leaf _ p hne hl hp, fun y hy => hy, fun q hq => hq⟩
  | branch id b l r hne hl hb hL hR hpL hpR ihL ihR =>
    simp only [idsFrom, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact ⟨_, Reads.branch _ b l r hne hl hb hL hR hpL hpR, fun y hy => hy, fun q hq => hq⟩
    · obtain ⟨u, hu, hids, hkeys⟩ := ihL hx
      exact ⟨u, hu, fun y hy => by simp [idsFrom, hids y hy], fun q hq => by simp [Trie.keys, hkeys hq]⟩
    · obtain ⟨u, hu, hids, hkeys⟩ := ihR hx
      exact ⟨u, hu, fun y hy => by simp [idsFrom, hids y hy], fun q hq => by simp [Trie.keys, hkeys hq]⟩

theorem Reads.parent_of {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) {x : ℕ}
    (hx : x ∈ idsFrom T id t) (hne : x ≠ id) :
    (T.nodes x).parent ∈ idsFrom T id t ∧ (T.nodes (T.nodes x).parent).leaf = false ∧
      ((T.nodes (T.nodes x).parent).left = x ∨ (T.nodes (T.nodes x).parent).right = x) := by
  induction h with
  | leaf id p _ _ _ => simp only [idsFrom, List.mem_singleton] at hx; exact absurd hx hne
  | branch id b l r _ hl _ hL hR hpL hpR ihL ihR =>
    simp only [idsFrom, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact absurd rfl hne
    · by_cases hxl : x = (T.nodes id).left
      · subst hxl
        refine ⟨by rw [hpL]; simp [idsFrom], by rw [hpL]; exact hl, by rw [hpL]; exact Or.inl rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ihL hx hxl
        exact ⟨by simp [idsFrom, h1], h2, h3⟩
    · by_cases hxr : x = (T.nodes id).right
      · subst hxr
        refine ⟨by rw [hpR]; simp [idsFrom], by rw [hpR]; exact hl, by rw [hpR]; exact Or.inr rfl⟩
      · obtain ⟨h1, h2, h3⟩ := ihR hx hxr
        exact ⟨by simp [idsFrom, h1], h2, h3⟩

theorem Reads.children_mem {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) {x : ℕ}
    (hx : x ∈ idsFrom T id t) (hbr : (T.nodes x).leaf = false) :
    (T.nodes x).left ∈ idsFrom T id t ∧ (T.nodes x).right ∈ idsFrom T id t := by
  obtain ⟨u, hu, hids, _⟩ := h.sub hx
  cases hu with
  | leaf _ _ _ hl _ => rw [hbr] at hl; exact absurd hl (by simp)
  | branch _ _ l r _ _ _ hL hR _ _ =>
    exact ⟨hids _ (by simp [idsFrom, mem_idsFrom_self]), hids _ (by simp [idsFrom, mem_idsFrom_self])⟩

theorem Reads.key_of_leaf {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) {x p : ℕ}
    (hx : x ∈ idsFrom T id t) (hleaf : Reads T x (Trie.leaf p)) : p ∈ t.keys := by
  obtain ⟨u, hu, _, hkeys⟩ := h.sub hx
  have := hu.unique hleaf; subst this
  exact hkeys (by simp [Trie.keys])

theorem Reads.ids_ne_zero {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) :
    ∀ x ∈ idsFrom T id t, x ≠ 0 := by
  intro x hx; obtain ⟨u, hu, _, _⟩ := h.sub hx; exact hu.ne_zero

theorem Reads.exists_leaf {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) {q : ℕ} (hq : q ∈ t.keys) :
    ∃ x ∈ idsFrom T id t, Reads T x (Trie.leaf q) := by
  induction h with
  | leaf id p hne hl hp =>
    simp only [Trie.keys, Finset.mem_singleton] at hq; subst hq
    exact ⟨id, by simp [idsFrom], Reads.leaf id _ hne hl hp⟩
  | branch id b l r _ _ _ _ _ _ _ ihL ihR =>
    simp only [Trie.keys, Finset.mem_union] at hq
    rcases hq with hq | hq
    · obtain ⟨x, hx, hr⟩ := ihL hq; exact ⟨x, by simp [idsFrom, hx], hr⟩
    · obtain ⟨x, hx, hr⟩ := ihR hq; exact ⟨x, by simp [idsFrom, hx], hr⟩

/-- Under `Wf`, a key is read by exactly one id. -/
theorem Reads.leaf_unique {T : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) (hw : Trie.Wf t) {q x y : ℕ}
    (hx : x ∈ idsFrom T id t) (hy : y ∈ idsFrom T id t)
    (hrx : Reads T x (Trie.leaf q)) (hry : Reads T y (Trie.leaf q)) : x = y := by
  induction h with
  | leaf id p _ _ _ =>
    simp only [idsFrom, List.mem_singleton] at hx hy; rw [hx, hy]
  | branch id b l r _ hl _ hL hR _ _ ihL ihR =>
    have hwl : Trie.Wf l := by cases hw; assumption
    have hwr : Trie.Wf r := by cases hw; assumption
    simp only [idsFrom, List.mem_cons, List.mem_append] at hx hy
    have hxid : x ≠ id := fun e => by subst e; cases hrx with | leaf _ _ _ hl' _ => rw [hl] at hl'; exact absurd hl' (by simp)
    have hyid : y ≠ id := fun e => by subst e; cases hry with | leaf _ _ _ hl' _ => rw [hl] at hl'; exact absurd hl' (by simp)
    rcases hx with rfl | hx | hx <;> rcases hy with rfl | hy | hy
    · rfl
    · exact absurd rfl hxid
    · exact absurd rfl hxid
    · exact absurd rfl hyid
    · exact ihL hwl hx hy
    · exact absurd (hL.key_of_leaf hx hrx) (fun hql => hw.not_both hql (hR.key_of_leaf hy hry))
    · exact absurd rfl hyid
    · exact absurd (hR.key_of_leaf hx hrx) (fun hqr => hw.not_both (hL.key_of_leaf hy hry) hqr)
    · exact ihR hwr hx hy

/-- Reading survives writes outside the read ids and a change of the root's parent field. -/
theorem Reads.mono_root {T T' : Tree} {id : ℕ} {t : Trie} (h : Reads T id t) (hnd : (idsFrom T id t).Nodup)
    (hsame : ∀ x ∈ idsFrom T id t, x ≠ id → T'.nodes x = T.nodes x)
    (hl : (T'.nodes id).left = (T.nodes id).left) (hr : (T'.nodes id).right = (T.nodes id).right)
    (hlf : (T'.nodes id).leaf = (T.nodes id).leaf) (hb : (T'.nodes id).bit = (T.nodes id).bit)
    (hp : (T'.nodes id).price = (T.nodes id).price) : Reads T' id t := by
  cases h with
  | leaf _ p hne hleaf hprice => exact Reads.leaf id p hne (by rw [hlf]; exact hleaf) (by rw [hp]; exact hprice)
  | branch _ b l r hne hleaf hbit hL hR hpL hpR =>
    simp only [idsFrom, List.nodup_cons, List.mem_append] at hnd
    have hidl : id ∉ idsFrom T (T.nodes id).left l := fun hx => hnd.1 (Or.inl hx)
    have hidr : id ∉ idsFrom T (T.nodes id).right r := fun hx => hnd.1 (Or.inr hx)
    have hL' : Reads T' (T.nodes id).left l :=
      hL.mono (fun x hx => hsame x (by simp [idsFrom, hx]) (fun e => hidl (by rw [e] at hx; exact hx)))
    have hR' : Reads T' (T.nodes id).right r :=
      hR.mono (fun x hx => hsame x (by simp [idsFrom, hx]) (fun e => hidr (by rw [e] at hx; exact hx)))
    have hcl : T'.nodes (T.nodes id).left = T.nodes (T.nodes id).left :=
      hsame _ (by simp [idsFrom, mem_idsFrom_self]) (fun e => hidl (by rw [e]; exact mem_idsFrom_self _ _ _))
    have hcr : T'.nodes (T.nodes id).right = T.nodes (T.nodes id).right :=
      hsame _ (by simp [idsFrom, mem_idsFrom_self]) (fun e => hidr (by rw [e]; exact mem_idsFrom_self _ _ _))
    refine Reads.branch id b l r hne (by rw [hlf]; exact hleaf) (by rw [hb]; exact hbit) ?_ ?_ ?_ ?_
    · rw [hl]; exact hL'
    · rw [hr]; exact hR'
    · rw [hl, hcl]; exact hpL
    · rw [hr, hcr]; exact hpR

theorem idsFrom_mono_lr {T T' : Tree} {id : ℕ} {t : Trie} (h : Reads T id t)
    (hsame : ∀ x ∈ idsFrom T id t, (T'.nodes x).left = (T.nodes x).left ∧ (T'.nodes x).right = (T.nodes x).right) :
    idsFrom T' id t = idsFrom T id t := by
  induction h with
  | leaf id p _ _ _ => rfl
  | branch id b l r _ _ _ hL hR _ _ ihL ihR =>
    obtain ⟨hl, hr⟩ := hsame id (by simp [idsFrom])
    simp only [idsFrom, hl, hr]
    rw [ihL (fun x hx => hsame x (by simp [idsFrom, hx])), ihR (fun x hx => hsame x (by simp [idsFrom, hx]))]

/-! ## Node lookups through the storage writes -/

namespace Tree

theorem nodes_setNode (T : Tree) (id : ℕ) (n : Node) (x : ℕ) :
    (T.setNode id n).nodes x = if x = id then n else T.nodes x := by
  simp [setNode, Function.update_apply]

theorem nodes_freeNode (T : Tree) (id x : ℕ) :
    (T.freeNode id).nodes x = if x = id then Node.empty else T.nodes x := by
  simp [freeNode, setNode, Function.update_apply]

@[simp] theorem root_setNode (T : Tree) id n : (T.setNode id n).root = T.root := rfl
@[simp] theorem root_freeNode (T : Tree) id : (T.freeNode id).root = T.root := rfl
@[simp] theorem root_setLeaf (T : Tree) p id : (T.setLeaf p id).root = T.root := rfl
@[simp] theorem nodes_setLeaf (T : Tree) p id : (T.setLeaf p id).nodes = T.nodes := rfl
@[simp] theorem leaves_setNode (T : Tree) id n : (T.setNode id n).leaves = T.leaves := rfl
@[simp] theorem leaves_freeNode (T : Tree) id : (T.freeNode id).leaves = T.leaves := rfl
@[simp] theorem freeIds_setNode (T : Tree) id n : (T.setNode id n).freeIds = T.freeIds := rfl
@[simp] theorem freeIds_freeNode (T : Tree) id : (T.freeNode id).freeIds = id :: T.freeIds := rfl
@[simp] theorem freeIds_setLeaf (T : Tree) p id : (T.setLeaf p id).freeIds = T.freeIds := rfl
@[simp] theorem nextNodeId_setNode (T : Tree) id n : (T.setNode id n).nextNodeId = T.nextNodeId := rfl
@[simp] theorem nextNodeId_freeNode (T : Tree) id : (T.freeNode id).nextNodeId = T.nextNodeId := rfl
@[simp] theorem nextNodeId_setLeaf (T : Tree) p id : (T.setLeaf p id).nextNodeId = T.nextNodeId := rfl

section Relink
variable (T : Tree) (leafId branchId siblingId grandId : ℕ) (goLeft : Bool)

theorem relink_nodes_other {x : ℕ} (h1 : x ≠ leafId) (h2 : x ≠ branchId) (h3 : x ≠ siblingId) (h4 : x ≠ grandId) :
    (T.relink leafId branchId siblingId grandId goLeft).nodes x = T.nodes x := by
  simp only [relink]
  split_ifs <;> simp [nodes_freeNode, nodes_setNode, h1, h2, h3, h4]

theorem relink_nodes_sibling (h1 : siblingId ≠ leafId) (h2 : siblingId ≠ branchId) (h3 : siblingId ≠ grandId) :
    (T.relink leafId branchId siblingId grandId goLeft).nodes siblingId = { T.nodes siblingId with parent := grandId } := by
  simp only [relink]
  split_ifs <;> simp [nodes_freeNode, nodes_setNode, h1, h2, h3]

theorem relink_nodes_grand (h0 : grandId ≠ 0) (h1 : grandId ≠ leafId) (h2 : grandId ≠ branchId) (h3 : grandId ≠ siblingId) :
    (T.relink leafId branchId siblingId grandId goLeft).nodes grandId =
      if goLeft then { T.nodes grandId with left := siblingId } else { T.nodes grandId with right := siblingId } := by
  simp only [relink]
  split_ifs with hg hgo <;> first | exact absurd hg h0 | simp [nodes_freeNode, nodes_setNode, h1, h2, h3, Ne.symm h3]

/-- The parent field of any id other than the sibling, the leaf and the branch is unchanged. -/
theorem relink_parent_other {x : ℕ} (h1 : x ≠ leafId) (h2 : x ≠ branchId) (h3 : x ≠ siblingId) :
    ((T.relink leafId branchId siblingId grandId goLeft).nodes x).parent = (T.nodes x).parent := by
  simp only [relink]
  split_ifs <;> simp [nodes_freeNode, nodes_setNode, h1, h2, h3] <;> split_ifs <;> simp_all

@[simp] theorem relink_root :
    (T.relink leafId branchId siblingId grandId goLeft).root = if grandId = 0 then siblingId else T.root := by
  simp only [relink, root_freeNode, root_setNode]; split_ifs <;> rfl
@[simp] theorem relink_leaves : (T.relink leafId branchId siblingId grandId goLeft).leaves = T.leaves := by
  simp only [relink]; split_ifs <;> rfl
@[simp] theorem relink_freeIds :
    (T.relink leafId branchId siblingId grandId goLeft).freeIds = leafId :: branchId :: T.freeIds := by
  simp only [relink]; split_ifs <;> rfl
@[simp] theorem relink_nextNodeId : (T.relink leafId branchId siblingId grandId goLeft).nextNodeId = T.nextNodeId := by
  simp only [relink]; split_ifs <;> rfl

end Relink
end Tree

/-! ## The removal lemmas -/

section Remove

variable {T : Tree} {p leafId branchId siblingId grandId : ℕ} {goLeft : Bool}

/-- Global facts about the four ids a removal touches, derived once from `Repr`. -/
structure RemoveCtx (T : Tree) (p leafId branchId siblingId grandId : ℕ) (goLeft : Bool) : Prop where
  leaf_reads : Reads T leafId (Trie.leaf p)
  leaf_parent : (T.nodes leafId).parent = branchId
  branch_branch : (T.nodes branchId).leaf = false
  branch_children : ((T.nodes branchId).left = leafId ∧ siblingId = (T.nodes branchId).right)
                  ∨ ((T.nodes branchId).right = leafId ∧ siblingId = (T.nodes branchId).left)
  sibling_parent : (T.nodes siblingId).parent = branchId
  grand_def : grandId = (T.nodes branchId).parent
  goLeft_def : goLeft = ((T.nodes grandId).left = branchId)
  grand_child : grandId ≠ 0 → (T.nodes grandId).leaf = false ∧
                  ((T.nodes grandId).left = branchId ∨ (T.nodes grandId).right = branchId)
  leaf_ne_branch : leafId ≠ branchId
  leaf_ne_sibling : leafId ≠ siblingId
  branch_ne_sibling : branchId ≠ siblingId
  grand_ne_branch : grandId ≠ branchId
  grand_ne_leaf : grandId ≠ leafId
  grand_ne_sibling : grandId ≠ siblingId

local notation "T4" => (T.relink leafId branchId siblingId grandId goLeft)

/-- Ids that the four touched ids can be, inside a subtree not containing the leaf: none except
    possibly the subtree's own root being the sibling. -/
theorem untouched_ids (C : RemoveCtx T p leafId branchId siblingId grandId goLeft)
    {id : ℕ} {t : Trie} (h : Reads T id t) (hnot : leafId ∉ idsFrom T id t) :
    ∀ x ∈ idsFrom T id t, x ≠ leafId ∧ x ≠ branchId ∧ x ≠ grandId ∧ (x ≠ id → x ≠ siblingId) := by
  have hb' : branchId ∈ idsFrom T id t → False := fun hbm => by
    obtain ⟨hL, hR⟩ := h.children_mem hbm C.branch_branch
    rcases C.branch_children with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact hnot (hl ▸ hL)
    · exact hnot (hr ▸ hR)
  intro x hx
  have hb : x ≠ branchId := fun e => hb' (e ▸ hx)
  refine ⟨fun e => hnot (e ▸ hx), hb, ?_, ?_⟩
  · intro e
    have h0 := h.ids_ne_zero _ hx
    obtain ⟨hbr, hch⟩ := C.grand_child (e ▸ h0)
    obtain ⟨hL, hR⟩ := h.children_mem hx (e ▸ hbr)
    rcases hch with hl | hr
    · exact hb' (by rw [← hl, ← e]; exact hL)
    · exact hb' (by rw [← hr, ← e]; exact hR)
  · intro hne e
    obtain ⟨hpar, _, _⟩ := h.parent_of hx hne
    rw [e, C.sibling_parent] at hpar
    exact hb' hpar

/-- **Lemma A.** A subtree not containing the leaf reads the same after the relink. -/
theorem reads_untouched (C : RemoveCtx T p leafId branchId siblingId grandId goLeft)
    {id : ℕ} {t : Trie} (h : Reads T id t) (hnd : (idsFrom T id t).Nodup) (hnot : leafId ∉ idsFrom T id t) :
    Reads T4 id t ∧ idsFrom T4 id t = idsFrom T id t := by
  have hu := untouched_ids C h hnot
  have hsame : ∀ x ∈ idsFrom T id t, x ≠ id → (T4).nodes x = T.nodes x := by
    intro x hx hne
    obtain ⟨h1, h2, h3, h4⟩ := hu x hx
    exact Tree.relink_nodes_other T _ _ _ _ _ h1 h2 (h4 hne) h3
  have hroot : ((T4).nodes id).left = (T.nodes id).left ∧ ((T4).nodes id).right = (T.nodes id).right ∧
      ((T4).nodes id).leaf = (T.nodes id).leaf ∧ ((T4).nodes id).bit = (T.nodes id).bit ∧
      ((T4).nodes id).price = (T.nodes id).price := by
    obtain ⟨h1, h2, h3, _⟩ := hu id (mem_idsFrom_self _ _ _)
    by_cases hs : id = siblingId
    · subst hs
      rw [Tree.relink_nodes_sibling T _ _ _ _ _ (Ne.symm C.leaf_ne_sibling) (Ne.symm C.branch_ne_sibling)
        (Ne.symm C.grand_ne_sibling)]
      simp
    · rw [Tree.relink_nodes_other T _ _ _ _ _ h1 h2 hs h3]; simp
  obtain ⟨hl, hr, hlf, hb, hp⟩ := hroot
  refine ⟨h.mono_root hnd hsame hl hr hlf hb hp, ?_⟩
  apply idsFrom_mono_lr h
  intro x hx
  by_cases hxid : x = id
  · subst hxid; exact ⟨hl, hr⟩
  · rw [hsame x hx hxid]; exact ⟨rfl, rfl⟩

/-- The id the parent should point at after the removal. -/
def newId (leafId branchId siblingId : ℕ) (id : ℕ) : ℕ := if id = branchId then siblingId else id

/-- **Lemma B.** The subtree containing the leaf (strictly below its root) reads `removeLeaf`. -/
theorem reads_removed (C : RemoveCtx T p leafId branchId siblingId grandId goLeft) :
    ∀ {id : ℕ} {t : Trie}, Reads T id t → Trie.Wf t → (idsFrom T id t).Nodup → leafId ∈ idsFrom T id t → id ≠ leafId →
    ∃ t', t.removeLeaf p = some t' ∧ Reads T4 (newId leafId branchId siblingId id) t' ∧
      (∀ y ∈ idsFrom T4 (newId leafId branchId siblingId id) t', y ∈ idsFrom T id t ∧ y ≠ leafId ∧ y ≠ branchId) ∧
      (idsFrom T4 (newId leafId branchId siblingId id) t').Nodup := by
  intro id t h
  induction h with
  | leaf id q _ _ _ =>
    intro _ _ hx hne; simp only [idsFrom, List.mem_singleton] at hx; exact absurd hx.symm hne
  | branch id b l r hne hl hb hL hR hpL hpR ihL ihR =>
    intro hw hnd hx hidne
    obtain ⟨hwl, hwr⟩ : Trie.Wf l ∧ Trie.Wf r := by cases hw with | branch hwl hwr _ _ _ => exact ⟨hwl, hwr⟩
    have hnd' := hnd
    simp only [idsFrom, List.nodup_cons, List.nodup_append, List.mem_append] at hnd
    obtain ⟨hid_notin, hndL, hndR, hdisj0⟩ := hnd
    have hdisj : ∀ a, a ∈ idsFrom T (T.nodes id).left l → a ∈ idsFrom T (T.nodes id).right r → False :=
      fun a h1 h2 => hdisj0 a h1 a h2 rfl
    simp only [idsFrom, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact absurd rfl hidne
    · -- the leaf is in the left subtree
      have hp_l : p ∈ l.keys := hL.key_of_leaf hx C.leaf_reads
      have hleaf_notin_r : leafId ∉ idsFrom T (T.nodes id).right r := fun hr => hdisj _ hx hr
      obtain ⟨hRr, hRids⟩ := reads_untouched C hR hndR hleaf_notin_r
      by_cases hlid : (T.nodes id).left = leafId
      · -- the leaf is the left child: `id` is the branch, the right child is the sibling
        have hbid : branchId = id := by rw [← C.leaf_parent, ← hlid]; exact hpL
        have hl_leaf : l = Trie.leaf p := hL.unique (hlid ▸ C.leaf_reads)
        have hsib : siblingId = (T.nodes id).right := by
          rcases C.branch_children with ⟨_, hs⟩ | ⟨hr, _⟩
          · rw [hs, hbid]
          · exfalso; rw [hbid] at hr
            exact hdisj leafId (by rw [← hlid]; exact mem_idsFrom_self _ _ _) (by rw [← hr]; exact mem_idsFrom_self _ _ _)
        subst hl_leaf
        have hnew : newId leafId branchId siblingId id = (T.nodes id).right := by simp [newId, hbid, hsib]
        refine ⟨r, by simp [Trie.removeLeaf, Trie.keys], ?_, ?_, ?_⟩
        · rw [hnew]; exact hRr
        · intro y hy
          rw [hnew, hRids] at hy
          refine ⟨by simp [idsFrom, hy], fun e => hdisj leafId (by rw [← hlid]; exact mem_idsFrom_self _ _ _) (by rw [← e]; exact hy),
            fun e => hid_notin (by rw [hbid] at e; exact Or.inr (by rw [e] at hy; exact hy))⟩
        · rw [hnew, hRids]; exact hndR
      · -- the leaf is deeper in the left subtree
        obtain ⟨l', hl', hRl, hidsL, hndL'⟩ := ihL hwl hndL hx hlid
        -- the branch is inside the left subtree, hence not `id`
        have hbr_in : branchId ∈ idsFrom T (T.nodes id).left l := by
          have := (hL.parent_of hx (Ne.symm hlid)).1; rwa [C.leaf_parent] at this
        have hbr_ne_id : branchId ≠ id := fun e => hid_notin (Or.inl (by rw [e] at hbr_in; exact hbr_in))
        have hsib_in : siblingId ∈ idsFrom T (T.nodes id).left l := by
          obtain ⟨hL', hR'⟩ := hL.children_mem hbr_in C.branch_branch
          rcases C.branch_children with ⟨_, hs⟩ | ⟨_, hs⟩
          · rw [hs]; exact hR'
          · rw [hs]; exact hL'
        have hsib_ne_id : siblingId ≠ id := fun e => hid_notin (Or.inl (by rw [e] at hsib_in; exact hsib_in))
        have hleaf_ne_id : leafId ≠ id := Ne.symm hidne
        have hrid_ne_leaf : (T.nodes id).right ≠ leafId := fun e => hdisj leafId hx (by rw [← e]; exact mem_idsFrom_self _ _ _)
        have hrid_ne_br : (T.nodes id).right ≠ branchId := fun e => hdisj branchId hbr_in (by rw [← e]; exact mem_idsFrom_self _ _ _)
        have hrid_ne_sib : (T.nodes id).right ≠ siblingId := fun e => hdisj siblingId hsib_in (by rw [← e]; exact mem_idsFrom_self _ _ _)
        have hids : idsFrom T4 (newId leafId branchId siblingId id) (Trie.branch b l' r)
            = id :: (idsFrom T4 (newId leafId branchId siblingId (T.nodes id).left) l' ++ idsFrom T4 (T.nodes id).right r) := by
          simp only [newId, hbr_ne_id.symm, ↓reduceIte, idsFrom]
          congr 2
          · by_cases hgl : (T.nodes id).left = branchId
            · have hgid : grandId = id := by rw [C.grand_def, ← hgl]; exact hpL
              have hgo : goLeft = true := by rw [C.goLeft_def, hgid, hgl]; try simp
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp [show (T.nodes grandId).left = branchId by rw [hgid]; exact hgl]
            · have hgne : grandId ≠ id := by
                intro e
                obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
                rcases hch with hc | hc
                · exact hgl (e ▸ hc)
                · exact hrid_ne_br (e ▸ hc)
              rw [Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)]
              simp [hgl]
          · by_cases hgl : (T.nodes id).left = branchId
            · have hgid : grandId = id := by rw [C.grand_def, ← hgl]; exact hpL
              have hgo : goLeft = true := by rw [C.goLeft_def, hgid, hgl]; try simp
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp
            · have hgne : grandId ≠ id := by
                intro e
                obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
                rcases hch with hc | hc
                · exact hgl (e ▸ hc)
                · exact hrid_ne_br (e ▸ hc)
              rw [Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)]
        refine ⟨Trie.branch b l' r, by simp [Trie.removeLeaf, hp_l, hl'], ?_, ?_, ?_⟩
        · simp only [newId, hbr_ne_id.symm, ↓reduceIte]
          by_cases hgl : (T.nodes id).left = branchId
          · -- the branch is the left child of `id`: `id` is the grandparent
            have hgid : grandId = id := by rw [C.grand_def, ← hgl]; exact hpL
            have hgo : goLeft = true := by rw [C.goLeft_def, hgid, hgl]; try simp
            have hnode : (T4).nodes id = { T.nodes id with left := siblingId } := by
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp
            simp only [newId, hgl, ↓reduceIte] at hRl
            refine Reads.branch id b l' r hne (by rw [hnode]; try exact hl) (by rw [hnode]; try exact hb) ?_ ?_ ?_ ?_
            · rw [hnode]; exact hRl
            · rw [hnode]; exact hRr
            · rw [hnode]; simp only
              rw [Tree.relink_nodes_sibling T _ _ _ _ _ (Ne.symm C.leaf_ne_sibling) (Ne.symm C.branch_ne_sibling)
                (Ne.symm C.grand_ne_sibling)]; simp [hgid]
            · rw [hnode]; simp only
              rw [Tree.relink_parent_other T _ _ _ _ _ hrid_ne_leaf hrid_ne_br hrid_ne_sib]; try exact hpR
          · -- the branch is deeper: `id` is untouched
            have hgne : grandId ≠ id := by
              intro e
              obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
              rcases hch with hc | hc
              · exact hgl (e ▸ hc)
              · exact hrid_ne_br (e ▸ hc)
            have hnode : (T4).nodes id = T.nodes id :=
              Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)
            simp only [newId, hgl, ↓reduceIte] at hRl
            have hlid_ne_sib : (T.nodes id).left ≠ siblingId := by
              intro e
              have := C.sibling_parent; rw [← e, hpL] at this; exact hbr_ne_id this.symm
            refine Reads.branch id b l' r hne (by rw [hnode]; try exact hl) (by rw [hnode]; try exact hb) ?_ ?_ ?_ ?_
            · rw [hnode]; exact hRl
            · rw [hnode]; exact hRr
            · rw [hnode]
              rw [Tree.relink_parent_other T _ _ _ _ _ hlid hgl hlid_ne_sib]; exact hpL
            · rw [hnode]
              rw [Tree.relink_parent_other T _ _ _ _ _ hrid_ne_leaf hrid_ne_br hrid_ne_sib]; try exact hpR
        · -- ids of the result
          intro y hy
          rw [hids] at hy
          simp only [List.mem_cons, List.mem_append, hRids] at hy
          rcases hy with rfl | hy | hy
          · exact ⟨by simp [idsFrom], hidne, hbr_ne_id.symm⟩
          · obtain ⟨h1, h2, h3⟩ := hidsL y hy; exact ⟨by simp [idsFrom, h1], h2, h3⟩
          · exact ⟨by simp [idsFrom, hy], fun e => hdisj leafId hx (by rw [← e]; exact hy), fun e => hdisj branchId hbr_in (by rw [← e]; exact hy)⟩
        · rw [hids, hRids]
          simp only [List.nodup_cons, List.nodup_append, List.mem_append]
          refine ⟨?_, hndL', hndR, ?_⟩
          · rintro (hy | hy)
            · exact hid_notin (Or.inl (hidsL _ hy).1)
            · exact hid_notin (Or.inr hy)
          · intro a ha c hc e
            exact hdisj a (hidsL a ha).1 (by rw [e]; exact hc)
    · -- the leaf is in the right subtree
      have hp_r : p ∈ r.keys := hR.key_of_leaf hx C.leaf_reads
      have hp_nl : p ∉ l.keys := fun hpl => hw.not_both hpl hp_r
      have hleaf_notin_l : leafId ∉ idsFrom T (T.nodes id).left l := fun hl => hdisj _ hl hx
      obtain ⟨hLl, hLids⟩ := reads_untouched C hL hndL hleaf_notin_l
      by_cases hrid : (T.nodes id).right = leafId
      · -- the leaf is the right child: `id` is the branch, the left child is the sibling
        have hbid : branchId = id := by rw [← C.leaf_parent, ← hrid]; exact hpR
        have hr_leaf : r = Trie.leaf p := hR.unique (hrid ▸ C.leaf_reads)
        have hsib : siblingId = (T.nodes id).left := by
          rcases C.branch_children with ⟨hl, _⟩ | ⟨_, hs⟩
          · exfalso; rw [hbid] at hl
            exact hdisj leafId (by rw [← hl]; exact mem_idsFrom_self _ _ _) (by rw [← hrid]; exact mem_idsFrom_self _ _ _)
          · rw [hs, hbid]
        subst hr_leaf
        have hnew : newId leafId branchId siblingId id = (T.nodes id).left := by simp [newId, hbid, hsib]
        refine ⟨l, by simp [Trie.removeLeaf, Trie.keys, hp_nl], ?_, ?_, ?_⟩
        · rw [hnew]; exact hLl
        · intro y hy
          rw [hnew, hLids] at hy
          refine ⟨by simp [idsFrom, hy], fun e => hdisj leafId (by rw [← e]; exact hy) (by rw [← hrid]; exact mem_idsFrom_self _ _ _),
            fun e => hid_notin (by rw [hbid] at e; exact Or.inl (by rw [e] at hy; exact hy))⟩
        · rw [hnew, hLids]; exact hndL
      · -- the leaf is deeper in the right subtree
        obtain ⟨r', hr', hRr, hidsR, hndR'⟩ := ihR hwr hndR hx hrid
        have hbr_in : branchId ∈ idsFrom T (T.nodes id).right r := by
          have := (hR.parent_of hx (Ne.symm hrid)).1; rwa [C.leaf_parent] at this
        have hbr_ne_id : branchId ≠ id := fun e => hid_notin (Or.inr (by rw [e] at hbr_in; exact hbr_in))
        have hsib_in : siblingId ∈ idsFrom T (T.nodes id).right r := by
          obtain ⟨hL', hR'⟩ := hR.children_mem hbr_in C.branch_branch
          rcases C.branch_children with ⟨_, hs⟩ | ⟨_, hs⟩
          · rw [hs]; exact hR'
          · rw [hs]; exact hL'
        have hsib_ne_id : siblingId ≠ id := fun e => hid_notin (Or.inr (by rw [e] at hsib_in; exact hsib_in))
        have hleaf_ne_id : leafId ≠ id := Ne.symm hidne
        have hlid_ne_leaf : (T.nodes id).left ≠ leafId := fun e => hdisj leafId (by rw [← e]; exact mem_idsFrom_self _ _ _) hx
        have hlid_ne_br : (T.nodes id).left ≠ branchId := fun e => hdisj branchId (by rw [← e]; exact mem_idsFrom_self _ _ _) hbr_in
        have hlid_ne_sib : (T.nodes id).left ≠ siblingId := fun e => hdisj siblingId (by rw [← e]; exact mem_idsFrom_self _ _ _) hsib_in
        have hids : idsFrom T4 (newId leafId branchId siblingId id) (Trie.branch b l r')
            = id :: (idsFrom T4 (T.nodes id).left l ++ idsFrom T4 (newId leafId branchId siblingId (T.nodes id).right) r') := by
          simp only [newId, hbr_ne_id.symm, ↓reduceIte, idsFrom]
          congr 2
          · by_cases hgr : (T.nodes id).right = branchId
            · have hgid : grandId = id := by rw [C.grand_def, ← hgr]; exact hpR
              have hgo : goLeft = false := by have h := C.goLeft_def; rw [hgid] at h; simpa [hlid_ne_br] using h
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp
            · have hgne : grandId ≠ id := by
                intro e
                obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
                rcases hch with hc | hc
                · exact hlid_ne_br (e ▸ hc)
                · exact hgr (e ▸ hc)
              rw [Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)]
          · by_cases hgr : (T.nodes id).right = branchId
            · have hgid : grandId = id := by rw [C.grand_def, ← hgr]; exact hpR
              have hgo : goLeft = false := by have h := C.goLeft_def; rw [hgid] at h; simpa [hlid_ne_br] using h
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp [show (T.nodes grandId).right = branchId by rw [hgid]; exact hgr]
            · have hgne : grandId ≠ id := by
                intro e
                obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
                rcases hch with hc | hc
                · exact hlid_ne_br (e ▸ hc)
                · exact hgr (e ▸ hc)
              rw [Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)]
              simp [hgr]
        refine ⟨Trie.branch b l r', by simp [Trie.removeLeaf, hp_nl, hr'], ?_, ?_, ?_⟩
        · simp only [newId, hbr_ne_id.symm, ↓reduceIte]
          by_cases hgr : (T.nodes id).right = branchId
          · -- the branch is the right child of `id`: `id` is the grandparent
            have hgid : grandId = id := by rw [C.grand_def, ← hgr]; exact hpR
            have hgo : goLeft = false := by have h := C.goLeft_def; rw [hgid] at h; simpa [hlid_ne_br] using h
            have hnode : (T4).nodes id = { T.nodes id with right := siblingId } := by
              rw [← hgid, Tree.relink_nodes_grand T _ _ _ _ _ (hgid ▸ hne) C.grand_ne_leaf C.grand_ne_branch
                C.grand_ne_sibling, hgo]; simp
            simp only [newId, hgr, ↓reduceIte] at hRr
            refine Reads.branch id b l r' hne (by rw [hnode]; try exact hl) (by rw [hnode]; try exact hb) ?_ ?_ ?_ ?_
            · rw [hnode]; exact hLl
            · rw [hnode]; exact hRr
            · rw [hnode]
              rw [Tree.relink_parent_other T _ _ _ _ _ hlid_ne_leaf hlid_ne_br hlid_ne_sib]; try exact hpL
            · rw [hnode]; simp only
              rw [Tree.relink_nodes_sibling T _ _ _ _ _ (Ne.symm C.leaf_ne_sibling) (Ne.symm C.branch_ne_sibling)
                (Ne.symm C.grand_ne_sibling)]; simp [hgid]
          · -- the branch is deeper: `id` is untouched
            have hgne : grandId ≠ id := by
              intro e
              obtain ⟨_, hch⟩ := C.grand_child (e ▸ hne)
              rcases hch with hc | hc
              · exact hlid_ne_br (e ▸ hc)
              · exact hgr (e ▸ hc)
            have hnode : (T4).nodes id = T.nodes id :=
              Tree.relink_nodes_other T _ _ _ _ _ hleaf_ne_id.symm hbr_ne_id.symm hsib_ne_id.symm (Ne.symm hgne)
            simp only [newId, hgr, ↓reduceIte] at hRr
            have hrid_ne_sib : (T.nodes id).right ≠ siblingId := by
              intro e
              have := C.sibling_parent; rw [← e, hpR] at this; exact hbr_ne_id this.symm
            refine Reads.branch id b l r' hne (by rw [hnode]; try exact hl) (by rw [hnode]; try exact hb) ?_ ?_ ?_ ?_
            · rw [hnode]; exact hLl
            · rw [hnode]; exact hRr
            · rw [hnode]
              rw [Tree.relink_parent_other T _ _ _ _ _ hlid_ne_leaf hlid_ne_br hlid_ne_sib]; try exact hpL
            · rw [hnode]
              rw [Tree.relink_parent_other T _ _ _ _ _ hrid hgr hrid_ne_sib]; try exact hpR
        · -- ids of the result
          intro y hy
          rw [hids] at hy
          simp only [List.mem_cons, List.mem_append, hLids] at hy
          rcases hy with rfl | hy | hy
          · exact ⟨by simp [idsFrom], hidne, hbr_ne_id.symm⟩
          · exact ⟨by simp [idsFrom, hy], fun e => hdisj leafId (by rw [← e]; exact hy) hx, fun e => hdisj branchId (by rw [← e]; exact hy) hbr_in⟩
          · obtain ⟨h1, h2, h3⟩ := hidsR y hy; exact ⟨by simp [idsFrom, h1], h2, h3⟩
        · rw [hids, hLids]
          simp only [List.nodup_cons, List.nodup_append, List.mem_append]
          refine ⟨?_, hndL, hndR', ?_⟩
          · rintro (hy | hy)
            · exact hid_notin (Or.inl hy)
            · exact hid_notin (Or.inr (hidsR _ hy).1)
          · intro a ha c hc e
            exact hdisj a ha (by rw [e]; exact (hidsR c hc).1)

end Remove

end AsyncSwap
