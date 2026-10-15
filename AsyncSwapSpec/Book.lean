import AsyncSwapSpec.Match
import AsyncSwapSpec.Reduce
import AsyncSwapSpec.Fee

/-!
# Pool state machine and escrow invariant

One pool of the `AsyncSwap` hook, with currency1 as the numeraire (USDC).  The state holds
the per-order storage (`AsyncFiller.State.orders`), the executor grants, and the hook's
ERC-6909 claim balances in the PoolManager.

`PoolState.Inv` is the Lean form of the Foundry invariant
`invariant_escrowEqualsOutstandingObligations` (test/MatchingInvariant.t.sol): the hook's
claims in each currency equal the sum, over open orders, of remaining input plus escrowed
priority bids.  Every transition is modelled with the *same* claim mutations the Solidity
performs (`settle(.., true)` burns claims, `take(.., true)` mints them) and is proved to
preserve the invariant.

Transitions return `none` exactly where the contract reverts.
-/

namespace AsyncSwap

structure PoolState where
  orders : OrderId → Order
  openIds : Finset OrderId
  isExecutor : Address → Address → Bool
  /-- Hook's ERC-6909 balance of currency0 in the PoolManager. -/
  claims0 : ℕ
  /-- Hook's ERC-6909 balance of currency1 (numeraire). -/
  claims1 : ℕ
  /-- `Book.orderingMode == PriorityFee`. -/
  priorityMode : Bool

namespace PoolState

/-- Sum of a per-order quantity over the open orders. -/
def owedBy (g : Order → ℕ) (s : PoolState) : ℕ := ∑ id ∈ s.openIds, g (s.orders id)

def owed0 (s : PoolState) : ℕ := s.owedBy Order.escrow0
def owed1 (s : PoolState) : ℕ := s.owedBy Order.escrow1

/-- The protocol invariant. -/
structure Inv (s : PoolState) : Prop where
  claims0 : s.claims0 = s.owed0
  claims1 : s.claims1 = s.owed1
  wf : ∀ id ∈ s.openIds, (s.orders id).wf

/-! ## Primitive storage effects -/

def withOrder (s : PoolState) (id : OrderId) (o : Order) : PoolState :=
  { s with orders := Function.update s.orders id o }

def openInsert (s : PoolState) (id : OrderId) : PoolState :=
  { s with openIds := insert id s.openIds }

/-- `delete self.orders[id]` + `_remove`. -/
def eraseOrder (s : PoolState) (id : OrderId) : PoolState :=
  { s with openIds := s.openIds.erase id }

/-- `take(input, hook, n, true)`: mint `n` claims of the order's input currency. -/
def mintInput (s : PoolState) (zeroForOne : Bool) (n : ℕ) : PoolState :=
  { s with claims0 := s.claims0 + (if zeroForOne then n else 0),
           claims1 := s.claims1 + (if zeroForOne then 0 else n) }

/-- `settle(input, hook, n, true)`: burn `n` claims of the order's input currency. -/
def burnInput (s : PoolState) (zeroForOne : Bool) (n : ℕ) : PoolState :=
  { s with claims0 := s.claims0 - (if zeroForOne then n else 0),
           claims1 := s.claims1 - (if zeroForOne then 0 else n) }

/-- `settle(numeraire, hook, n, true)` inside `settlePriorityFee` (donate or forfeit). -/
def burnNumeraire (s : PoolState) (n : ℕ) : PoolState := { s with claims1 := s.claims1 - n }

/-! ## Sum lemmas -/

theorem sum_insert_update (g : Order → ℕ) (f : OrderId → Order) (S : Finset OrderId)
    (id : OrderId) (o : Order) (h : id ∉ S) :
    ∑ x ∈ insert id S, g (Function.update f id o x) = g o + ∑ x ∈ S, g (f x) := by
  rw [Finset.sum_insert h, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl (fun x hx => by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hx h)])

theorem sum_erase (g : Order → ℕ) (f : OrderId → Order) (S : Finset OrderId)
    (id : OrderId) (h : id ∈ S) :
    ∑ x ∈ S.erase id, g (f x) + g (f id) = ∑ x ∈ S, g (f x) :=
  Finset.sum_erase_add _ _ h

theorem sum_update (g : Order → ℕ) (f : OrderId → Order) (S : Finset OrderId)
    (id : OrderId) (o : Order) (h : id ∈ S) :
    ∑ x ∈ S, g (Function.update f id o x) + g (f id) = ∑ x ∈ S, g (f x) + g o := by
  rw [← Finset.sum_erase_add _ _ h, ← Finset.sum_erase_add S _ h, Function.update_self]
  have : ∑ x ∈ S.erase id, g (Function.update f id o x) = ∑ x ∈ S.erase id, g (f x) :=
    Finset.sum_congr rfl (fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
  rw [this]; ring

/-! ## Transitions -/

/-- `_beforeSwap` + `_createOrder` + `AsyncFiller.addOrder`: escrow the whole deposit as a
    claim and open the order.  `executor` is the swap caller, which the hook binds to
    `hookData.executor` and requires to be authorised by the maker. -/
def create (s : PoolState) (id : OrderId) (executor : Address) (o : Order) : Option PoolState :=
  if id ∉ s.openIds ∧ s.isExecutor o.owner executor = true
     ∧ 0 < o.amountIn ∧ 0 < o.amountOutMin
     ∧ (s.priorityMode = false → o.priorityFee = 0)
     ∧ (s.priorityMode = true → minPriorityFee ≤ o.priorityFee)
     ∧ o.priorityFee ≤ maxPriorityFee then
    some (((s.mintInput o.zeroForOne o.amountIn).withOrder id
            { o with priorityFeeEscrowed := decide (o.priorityFee = 0) }).openInsert id)
  else none

/-- `recordPriorityFee`: the router escrows the bid as a numeraire claim in the same tx. -/
def recordPriorityFee (s : PoolState) (id : OrderId) (amount : ℕ) : Option PoolState :=
  if id ∈ s.openIds ∧ (s.orders id).priorityFeeEscrowed = false
     ∧ (s.orders id).priorityFee = amount ∧ amount ≠ 0 then
    some ({ s with claims1 := s.claims1 + amount }.withOrder id
            { s.orders id with priorityFeeEscrowed := true })
  else none

/-- What a full fill pays out (`AsyncFiller.fill`). -/
structure FillSettlement where
  /-- gross output the filler has settled: `amountOutMin + fee`. -/
  fillerPays : ℕ
  makerReceives : ℕ
  vaultReceives : ℕ
  /-- maker's input, paid to the filler. -/
  fillerReceives : ℕ
  deriving Repr

/-- Shared closing effect of `fill`, `cancel` and `fillFromPoolLiquidity`: burn the input
    escrow, settle the bid, delete the order. -/
def closeOrder (s : PoolState) (id : OrderId) : PoolState :=
  ((s.burnInput (s.orders id).zeroForOne (s.orders id).amountIn).burnNumeraire
      (s.orders id).priorityFee).eraseOrder id

/-- `AsyncFiller.fill`: full fill by an authorised executor. -/
def fill (s : PoolState) (id : OrderId) (executor : Address) :
    Option (PoolState × FillSettlement) :=
  if id ∈ s.openIds ∧ s.isExecutor (s.orders id).owner executor = true
     ∧ ((s.orders id).priorityFee ≠ 0 → (s.orders id).priorityFeeEscrowed = true) then
    some (s.closeOrder id,
          { fillerPays := (s.orders id).amountOutMin + poolFee (s.orders id).amountOutMin,
            makerReceives := (s.orders id).amountOutMin,
            vaultReceives := poolFee (s.orders id).amountOutMin,
            fillerReceives := (s.orders id).amountIn })
  else none

/-- `AsyncFiller.cancel`: executor is the owner or an authorised executor; refund `amountIn`. -/
def cancel (s : PoolState) (id : OrderId) (executor : Address) : Option (PoolState × ℕ) :=
  if id ∈ s.openIds
     ∧ (executor = (s.orders id).owner ∨ s.isExecutor (s.orders id).owner executor = true)
     ∧ ((s.orders id).priorityFee ≠ 0 → (s.orders id).priorityFeeEscrowed = true) then
    some (s.closeOrder id, (s.orders id).amountIn)
  else none

/-- `AsyncFiller.updatePrice`: maker-only; pure storage change, no claims move. -/
def updatePrice (s : PoolState) (id : OrderId) (caller : Address) (newMin : ℕ) :
    Option PoolState :=
  if caller = (s.orders id).owner ∧ newMin ≠ 0 ∧ id ∈ s.openIds then
    some (s.withOrder id { s.orders id with amountOutMin := newMin })
  else none

/-- `AsyncMatching.fillFromPoolLiquidity`: the whole input is swapped through the pool;
    the maker receives `amountOut ≥ amountOutMin` or the call reverts. -/
def liquidityFill (s : PoolState) (id : OrderId) (amountOut : ℕ) : Option (PoolState × ℕ) :=
  if id ∈ s.openIds ∧ (s.orders id).amountOutMin ≤ amountOut
     ∧ ((s.orders id).priorityFee ≠ 0 → (s.orders id).priorityFeeEscrowed = true) then
    some (s.closeOrder id, amountOut)
  else none

/-- `_transferEscrow` + `_settleMatchedPriorityFee` + `_reduceAfterMatch` for one side of a
    match: burn the consumed input (it goes to the counterparty), donate the pro-rata bid,
    then either keep the reduced order or close it — refunding the unused input and settling
    the remaining bid. -/
def reduceAfterMatch (s : PoolState) (id : OrderId) (l : Leg) : PoolState :=
  -- `_transferEscrow` (consumed input to the counterparty) + `_settleMatchedPriorityFee`
  let s1 := burnNumeraire (burnInput s (s.orders id).zeroForOne l.used) ((s.orders id).donatedFee l)
  if ((s.orders id).reduce l).amountIn = 0 ∨ ((s.orders id).reduce l).amountOutMin = 0 then
    -- close: settle the unfilled bid, refund the unused input, delete
    eraseOrder
      (burnInput (burnNumeraire s1 ((s.orders id).reduce l).priorityFee)
        (s.orders id).zeroForOne ((s.orders id).reduce l).amountIn) id
  else
    withOrder s1 id ((s.orders id).reduce l)

/-- `_matchPair`: size the trade from the resting side, then reduce both orders. -/
def matchPair (s : PoolState) (sellId buyId : OrderId) (restingBuy : Bool) : Option PoolState :=
  if sellId ∈ s.openIds ∧ buyId ∈ s.openIds
     ∧ (s.orders sellId).isBuy = false ∧ (s.orders buyId).isBuy = true
     ∧ ((s.orders sellId).priorityFee ≠ 0 → (s.orders sellId).priorityFeeEscrowed = true)
     ∧ ((s.orders buyId).priorityFee ≠ 0 → (s.orders buyId).priorityFeeEscrowed = true)
     ∧ (matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).assetAmount ≠ 0
     ∧ (matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).quoteAmount ≠ 0 then
    some (reduceAfterMatch
            (reduceAfterMatch s sellId
              ⟨(matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).assetAmount,
               (matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).quoteAmount⟩)
            buyId
              ⟨(matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).quoteAmount,
               (matchAmounts (s.orders sellId) (s.orders buyId) restingBuy).assetAmount⟩)
  else none

/-! ## Invariant preservation -/

theorem inv_create {s s' : PoolState} {id : OrderId} {executor : Address} {o : Order}
    (hs : s.Inv) (h : s.create id executor o = some s') : s'.Inv := by
  unfold create at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨h1, _, hin, hmin, _, _, _⟩ := hc
  have c0 := hs.claims0
  have c1 := hs.claims1
  simp only [owed0, owed1, owedBy, Order.escrow0, Order.escrow1] at c0 c1
  refine ⟨?_, ?_, ?_⟩
  · simp only [owed0, owedBy, openInsert, withOrder, mintInput]
    rw [sum_insert_update _ _ _ _ _ h1]
    simp only [Order.escrow0]
    cases o.zeroForOne <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · simp only [owed1, owedBy, openInsert, withOrder, mintInput]
    rw [sum_insert_update _ _ _ _ _ h1]
    simp only [Order.escrow1]
    by_cases hf : o.priorityFee = 0 <;>
      cases o.zeroForOne <;> simp only [hf, Bool.false_eq_true, ↓reduceIte, decide_true,
        decide_false] <;> omega
  · intro x hx
    simp only [openInsert, withOrder, mintInput, Finset.mem_insert, Function.update_apply] at hx ⊢
    rcases hx with rfl | hx
    · simp only [↓reduceIte, Order.wf]; exact ⟨hin, hmin⟩
    · simp only [ne_of_mem_of_not_mem hx h1, ↓reduceIte]; exact hs.wf x hx

theorem inv_recordPriorityFee {s s' : PoolState} {id : OrderId} {amount : ℕ} (hs : s.Inv)
    (h : s.recordPriorityFee id amount = some s') : s'.Inv := by
  unfold recordPriorityFee at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hid, hnesc, hfee, _⟩ := hc
  have c0 := hs.claims0
  have c1 := hs.claims1
  simp only [owed0, owed1, owedBy, Order.escrow0, Order.escrow1] at c0 c1
  have u0 := sum_update Order.escrow0 s.orders s.openIds id
    { s.orders id with priorityFeeEscrowed := true } hid
  have u1 := sum_update Order.escrow1 s.orders s.openIds id
    { s.orders id with priorityFeeEscrowed := true } hid
  refine ⟨?_, ?_, ?_⟩
  · simp only [owed0, owedBy, withOrder]
    simp only [Order.escrow0] at u0 ⊢
    omega
  · simp only [owed1, owedBy, withOrder]
    simp only [Order.escrow1, hnesc, Bool.false_eq_true, ↓reduceIte] at u1 c1 ⊢
    omega
  · intro x hx
    simp only [withOrder, Function.update_apply]
    split_ifs with hxe
    · subst hxe; have := hs.wf x hx; simpa [Order.wf] using this
    · exact hs.wf x hx

/-- Closing an open order (fill / cancel / liquidity fill) preserves the invariant provided
    any non-zero bid was escrowed. -/
theorem inv_closeOrder {s : PoolState} {id : OrderId} (hs : s.Inv) (hid : id ∈ s.openIds)
    (hesc : (s.orders id).priorityFee ≠ 0 → (s.orders id).priorityFeeEscrowed = true) :
    (s.closeOrder id).Inv := by
  have c0 := hs.claims0
  have c1 := hs.claims1
  simp only [owed0, owed1, owedBy, Order.escrow0, Order.escrow1] at c0 c1
  have e0 := sum_erase Order.escrow0 s.orders s.openIds id hid
  have e1 := sum_erase Order.escrow1 s.orders s.openIds id hid
  refine ⟨?_, ?_, ?_⟩
  · simp only [owed0, owedBy, closeOrder, eraseOrder, burnNumeraire, burnInput]
    simp only [Order.escrow0] at e0 ⊢
    cases hz : (s.orders id).zeroForOne <;>
      simp only [hz, Bool.false_eq_true, ↓reduceIte] at e0 ⊢ <;> omega
  · simp only [owed1, owedBy, closeOrder, eraseOrder, burnNumeraire, burnInput]
    simp only [Order.escrow1] at e1 ⊢
    by_cases hf : (s.orders id).priorityFee = 0
    · cases hz : (s.orders id).zeroForOne <;>
        simp only [hz, hf, Bool.false_eq_true, ↓reduceIte] at e1 ⊢ <;> split_ifs at e1 <;> omega
    · have he := hesc hf
      cases hz : (s.orders id).zeroForOne <;>
        simp only [hz, he, Bool.false_eq_true, ↓reduceIte] at e1 ⊢ <;> omega
  · intro x hx
    simp only [closeOrder, eraseOrder, burnNumeraire, burnInput] at hx ⊢
    exact hs.wf x (Finset.mem_of_mem_erase hx)

theorem inv_fill {s s' : PoolState} {id : OrderId} {executor : Address} {st : FillSettlement}
    (hs : s.Inv) (h : s.fill id executor = some (s', st)) : s'.Inv := by
  unfold fill at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  exact inv_closeOrder hs hc.1 hc.2.2

theorem inv_cancel {s s' : PoolState} {id : OrderId} {executor : Address} {refund : ℕ}
    (hs : s.Inv) (h : s.cancel id executor = some (s', refund)) : s'.Inv := by
  unfold cancel at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  exact inv_closeOrder hs hc.1 hc.2.2

theorem inv_liquidityFill {s s' : PoolState} {id : OrderId} {amountOut out : ℕ}
    (hs : s.Inv) (h : s.liquidityFill id amountOut = some (s', out)) : s'.Inv := by
  unfold liquidityFill at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  exact inv_closeOrder hs hc.1 hc.2.2

theorem inv_updatePrice {s s' : PoolState} {id : OrderId} {caller : Address} {newMin : ℕ}
    (hs : s.Inv) (h : s.updatePrice id caller newMin = some s') : s'.Inv := by
  unfold updatePrice at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨_, hmin, hid⟩ := hc
  have c0 := hs.claims0
  have c1 := hs.claims1
  simp only [owed0, owed1, owedBy, Order.escrow0, Order.escrow1] at c0 c1
  have u0 := sum_update Order.escrow0 s.orders s.openIds id
    { s.orders id with amountOutMin := newMin } hid
  have u1 := sum_update Order.escrow1 s.orders s.openIds id
    { s.orders id with amountOutMin := newMin } hid
  refine ⟨?_, ?_, ?_⟩
  · simp only [owed0, owedBy, withOrder]
    simp only [Order.escrow0] at u0 ⊢
    omega
  · simp only [owed1, owedBy, withOrder]
    simp only [Order.escrow1] at u1 ⊢
    omega
  · intro x hx
    simp only [withOrder, Function.update_apply]
    split_ifs with hxe
    · subst hxe; have := hs.wf x hx; simp only [Order.wf] at this ⊢; omega
    · exact hs.wf x hx

/-- One side of a match preserves the invariant provided the leg is admissible and the bid,
    if any, was escrowed. -/
theorem inv_reduceAfterMatch {s : PoolState} {id : OrderId} {l : Leg} (hs : s.Inv)
    (hid : id ∈ s.openIds) (hleg : (s.orders id).legOk l)
    (hesc : (s.orders id).priorityFee ≠ 0 → (s.orders id).priorityFeeEscrowed = true) :
    (s.reduceAfterMatch id l).Inv := by
  obtain ⟨hpos, hle, _⟩ := hleg
  have hfee := Order.reduce_priorityFee (s.orders id) l hle
  have hin := Order.reduce_amountIn (s.orders id) l hle
  have hdon : (s.orders id).donatedFee l ≤ (s.orders id).priorityFee := mulDiv_le_of_le hle
  have hz' : ((s.orders id).reduce l).zeroForOne = (s.orders id).zeroForOne := rfl
  have he' : ((s.orders id).reduce l).priorityFeeEscrowed = (s.orders id).priorityFeeEscrowed := rfl
  have c0 := hs.claims0
  have c1 := hs.claims1
  simp only [owed0, owed1, owedBy, Order.escrow0, Order.escrow1] at c0 c1
  simp only [reduceAfterMatch]
  split_ifs with hclosed
  · -- closing branch: everything burned adds up to the order's full escrow
    have e0 := sum_erase Order.escrow0 s.orders s.openIds id hid
    have e1 := sum_erase Order.escrow1 s.orders s.openIds id hid
    simp only [Order.escrow0, Order.escrow1] at e0 e1
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [owed0, owedBy, eraseOrder, burnNumeraire, burnInput, Order.escrow0]
      cases hz : (s.orders id).zeroForOne <;>
        simp only [hz, Bool.false_eq_true, ↓reduceIte] at e0 ⊢ <;> omega
    · dsimp only [owed1, owedBy, eraseOrder, burnNumeraire, burnInput, Order.escrow1]
      cases hz : (s.orders id).zeroForOne <;> cases he : (s.orders id).priorityFeeEscrowed <;>
        simp only [hz, he, Bool.false_eq_true, ↓reduceIte, imp_false, ne_eq, not_not] at e1 hesc ⊢ <;>
        omega
    · intro x hx
      simp only [eraseOrder, burnNumeraire, burnInput] at hx ⊢
      exact hs.wf x (Finset.mem_of_mem_erase hx)
  · -- order stays open with reduced amounts
    have u0 := sum_update Order.escrow0 s.orders s.openIds id ((s.orders id).reduce l) hid
    have u1 := sum_update Order.escrow1 s.orders s.openIds id ((s.orders id).reduce l) hid
    have hwf' : ((s.orders id).reduce l).wf := Order.reduce_wf_of_not_closed _ _ hclosed
    simp only [Order.escrow0, Order.escrow1, hz', he'] at u0 u1
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [owed0, owedBy, withOrder, burnNumeraire, burnInput, Order.escrow0]
      cases hz : (s.orders id).zeroForOne <;>
        simp only [hz, Bool.false_eq_true, ↓reduceIte] at u0 ⊢ <;> omega
    · dsimp only [owed1, owedBy, withOrder, burnNumeraire, burnInput, Order.escrow1]
      cases hz : (s.orders id).zeroForOne <;> cases he : (s.orders id).priorityFeeEscrowed <;>
        simp only [hz, he, Bool.false_eq_true, ↓reduceIte, imp_false, ne_eq, not_not] at u1 hesc ⊢ <;>
        omega
    · intro x hx
      simp only [withOrder, burnNumeraire, burnInput, Function.update_apply] at hx ⊢
      split_ifs with hxe
      · exact hwf'
      · exact hs.wf x hx

/-- Both legs of a `_matchAmounts` result are admissible for their respective orders. -/
theorem matchAmounts_legOk (sell buy : Order) (rb : Bool)
    (hs : 0 < sell.amountIn) (hb : 0 < buy.amountIn)
    (ha : (matchAmounts sell buy rb).assetAmount ≠ 0)
    (hq : (matchAmounts sell buy rb).quoteAmount ≠ 0) :
    sell.legOk ⟨(matchAmounts sell buy rb).assetAmount, (matchAmounts sell buy rb).quoteAmount⟩
    ∧ buy.legOk ⟨(matchAmounts sell buy rb).quoteAmount, (matchAmounts sell buy rb).assetAmount⟩ := by
  have hsound := matchAmounts_sound sell buy rb hs hb _ rfl ha hq
  exact ⟨⟨Nat.pos_of_ne_zero ha, hsound.asset_le_sell_escrow, hsound.seller_limit⟩,
         ⟨Nat.pos_of_ne_zero hq, hsound.quote_le_buy_escrow, hsound.buyer_limit⟩⟩

theorem reduceAfterMatch_orders_ne (s : PoolState) (id x : OrderId) (l : Leg) (hx : x ≠ id) :
    (s.reduceAfterMatch id l).orders x = s.orders x := by
  simp only [reduceAfterMatch]
  split_ifs <;> simp [eraseOrder, burnNumeraire, burnInput, withOrder, Function.update_of_ne hx]

theorem reduceAfterMatch_mem (s : PoolState) (id x : OrderId) (l : Leg) (hx : x ≠ id)
    (h : x ∈ s.openIds) : x ∈ (s.reduceAfterMatch id l).openIds := by
  simp only [reduceAfterMatch]
  split_ifs <;> simp [eraseOrder, burnNumeraire, burnInput, withOrder, hx, h]

/-- **Matching preserves the escrow invariant.** -/
theorem inv_matchPair {s s' : PoolState} {sellId buyId : OrderId} {rb : Bool} (hs : s.Inv)
    (h : s.matchPair sellId buyId rb = some s') : s'.Inv := by
  unfold matchPair at h
  split_ifs at h with hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hsell, hbuy, hsb, hbb, hescS, hescB, ha, hq⟩ := hc
  have hne : buyId ≠ sellId := by
    intro e; rw [e, hsb] at hbb; exact Bool.false_ne_true hbb
  have hwfs := hs.wf sellId hsell
  have hwfb := hs.wf buyId hbuy
  obtain ⟨hlegS, hlegB⟩ :=
    matchAmounts_legOk (s.orders sellId) (s.orders buyId) rb hwfs.1 hwfb.1 ha hq
  have hs1 := inv_reduceAfterMatch hs hsell hlegS hescS
  have hmem := reduceAfterMatch_mem s sellId buyId
    ⟨(matchAmounts (s.orders sellId) (s.orders buyId) rb).assetAmount,
     (matchAmounts (s.orders sellId) (s.orders buyId) rb).quoteAmount⟩ hne hbuy
  have hord := reduceAfterMatch_orders_ne s sellId buyId
    ⟨(matchAmounts (s.orders sellId) (s.orders buyId) rb).assetAmount,
     (matchAmounts (s.orders sellId) (s.orders buyId) rb).quoteAmount⟩ hne
  exact inv_reduceAfterMatch hs1 hmem (by rw [hord]; exact hlegB) (by rw [hord]; exact hescB)

/-! ## Authorisation and settlement facts -/

theorem fill_requires_executor {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) :
    s.isExecutor (s.orders id).owner executor = true := by
  unfold fill at h; split_ifs at h with hc; exact hc.2.1

theorem fill_requires_open {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) : id ∈ s.openIds := by
  unfold fill at h; split_ifs at h with hc; exact hc.1

/-- A filled order is gone: it cannot be filled or cancelled again. -/
theorem fill_closes {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) : id ∉ s'.openIds := by
  unfold fill at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  simp [closeOrder, eraseOrder, burnNumeraire, burnInput]

/-- The filler's gross payment is split exactly between maker and vault. -/
theorem fill_output_conserved {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) :
    st.fillerPays = st.makerReceives + st.vaultReceives := by
  unfold fill at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h; rfl

/-- The maker receives exactly the stored `amountOutMin`, the filler exactly `amountIn`. -/
theorem fill_amounts {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) :
    st.makerReceives = (s.orders id).amountOutMin ∧ st.fillerReceives = (s.orders id).amountIn := by
  unfold fill at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- The vault's cut is 30 bps of gross, rounded down. -/
theorem fill_fee_is_30bps {s s' : PoolState} {st : FillSettlement} {id : OrderId}
    {executor : Address} (h : s.fill id executor = some (s', st)) :
    st.vaultReceives = 3 * st.fillerPays / 1000 := by
  unfold fill at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact poolFee_eq_30bps_of_gross _

theorem cancel_requires_owner_or_executor {s s' : PoolState} {r : ℕ} {id : OrderId}
    {executor : Address} (h : s.cancel id executor = some (s', r)) :
    executor = (s.orders id).owner ∨ s.isExecutor (s.orders id).owner executor = true := by
  unfold cancel at h; split_ifs at h with hc; exact hc.2.1

/-- Cancel refunds exactly the remaining escrow to the owner. -/
theorem cancel_refund {s s' : PoolState} {r : ℕ} {id : OrderId} {executor : Address}
    (h : s.cancel id executor = some (s', r)) : r = (s.orders id).amountIn := by
  unfold cancel at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem cancel_closes {s s' : PoolState} {r : ℕ} {id : OrderId} {executor : Address}
    (h : s.cancel id executor = some (s', r)) : id ∉ s'.openIds := by
  unfold cancel at h; split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  simp [closeOrder, eraseOrder, burnNumeraire, burnInput]

theorem updatePrice_requires_owner {s s' : PoolState} {id : OrderId} {caller : Address}
    {newMin : ℕ} (h : s.updatePrice id caller newMin = some s') :
    caller = (s.orders id).owner := by
  unfold updatePrice at h; split_ifs at h with hc; exact hc.1

/-- Repricing never moves claims. -/
theorem updatePrice_claims {s s' : PoolState} {id : OrderId} {caller : Address} {newMin : ℕ}
    (h : s.updatePrice id caller newMin = some s') :
    s'.claims0 = s.claims0 ∧ s'.claims1 = s.claims1 := by
  unfold updatePrice at h; split_ifs at h
  simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- A liquidity fill never pays the maker below their minimum. -/
theorem liquidityFill_meets_min {s s' : PoolState} {out : ℕ} {id : OrderId} {amountOut : ℕ}
    (h : s.liquidityFill id amountOut = some (s', out)) : (s.orders id).amountOutMin ≤ out := by
  unfold liquidityFill at h; split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h; exact hc.2.1

/-- Nobody other than the maker, or an executor the maker authorised, can release an open
    order's escrow through `fill` or `cancel`. -/
theorem no_unauthorized_close {s : PoolState} {id : OrderId} {actor : Address}
    (hnotOwner : actor ≠ (s.orders id).owner)
    (hnotExec : s.isExecutor (s.orders id).owner actor = false) :
    (∀ s' st, s.fill id actor ≠ some (s', st)) ∧ (∀ s' r, s.cancel id actor ≠ some (s', r)) := by
  refine ⟨fun s' st h => ?_, fun s' r h => ?_⟩
  · have := fill_requires_executor h; simp_all
  · rcases cancel_requires_owner_or_executor h with h | h <;> simp_all

end PoolState
end AsyncSwap
