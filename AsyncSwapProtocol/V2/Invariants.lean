import AsyncSwapProtocol.V2.Settlement

/-!
# v2 protocol specification — part 3: escrow invariant

`Escrow`: for each currency, the hook's ERC-6909 claims equal the sum over open orders of the
remaining input plus the escrowed bid (the Foundry invariant
`invariant_escrowEqualsOutstandingObligations`), with the storage well-formedness it needs:
open orders have positive input and are owned by users (not the hook, not the PoolManager).
Preserved by every v2 entry point, including the match loop — the matched sides use the
verified `AsyncSwap.Order.reduce` accounting (`reduce_amountIn`, `reduce_priorityFee`).
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-- What one open order obliges the hook to hold in currency `c`. -/
def escrowOf (c : Currency) (k : OrderKey) (i : OrderInfo) : ℤ :=
  (if k.input = c then (i.amountIn : ℤ) else 0)
  + (if c = numeraire then (if i.escrowed = true then (i.priorityFee : ℤ) else 0) else 0)

def owed (c : Currency) (w : World) : ℤ := ∑ k ∈ w.openKeys, escrowOf c k (w.orders k)

theorem Order.key_input (o : Order) : o.key.input = !o.zeroForOne := rfl
theorem Order.key_output (o : Order) : o.key.output = o.zeroForOne := rfl

structure Escrow (cfg : Config) (w : World) : Prop where
  claims : ∀ c, w.claims c cfg.hook = owed c w
  wf : ∀ k ∈ w.openKeys, 0 < (w.orders k).amountIn
  owner_ne_hook : ∀ k ∈ w.openKeys, k.owner ≠ cfg.hook
  owner_ne_pm : ∀ k ∈ w.openKeys, k.owner ≠ cfg.pm

/-! ### Sum lemmas -/

theorem sum_insert_update (g : OrderKey → OrderInfo → ℤ) (f : OrderKey → OrderInfo) (S : Finset OrderKey)
    (k : OrderKey) (i : OrderInfo) (h : k ∉ S) :
    ∑ x ∈ insert k S, g x (Function.update f k i x) = g k i + ∑ x ∈ S, g x (f x) := by
  rw [Finset.sum_insert h, Function.update_self]
  congr 1
  exact Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hx h)])

theorem sum_erase_update (g : OrderKey → OrderInfo → ℤ) (f : OrderKey → OrderInfo) (S : Finset OrderKey)
    (k : OrderKey) (i : OrderInfo) (h : k ∈ S) :
    ∑ x ∈ S.erase k, g x (Function.update f k i x) = ∑ x ∈ S, g x (f x) - g k (f k) := by
  rw [← Finset.sum_erase_add S _ h]
  have : ∑ x ∈ S.erase k, g x (Function.update f k i x) = ∑ x ∈ S.erase k, g x (f x) :=
    Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
  rw [this]; ring

theorem sum_update (g : OrderKey → OrderInfo → ℤ) (f : OrderKey → OrderInfo) (S : Finset OrderKey)
    (k : OrderKey) (i : OrderInfo) (h : k ∈ S) :
    ∑ x ∈ S, g x (Function.update f k i x) = ∑ x ∈ S, g x (f x) - g k (f k) + g k i := by
  rw [← Finset.sum_erase_add _ _ h, ← Finset.sum_erase_add S _ h, Function.update_self]
  have : ∑ x ∈ S.erase k, g x (Function.update f k i x) = ∑ x ∈ S.erase k, g x (f x) :=
    Finset.sum_congr rfl (fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)])
  rw [this]; ring

/-! ### `openKeys` through the primitives -/

@[simp] theorem openKeys_transfer (t : Tx) c s d n : (t.transfer c s d n).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_mint (t : Tx) c d n b : (t.mint c d n b).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_burn (t : Tx) c s n b : (t.burn c s n b).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_donate (t : Tx) c n b : (t.donate c n b).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_poolSwap (t : Tx) ci co ai ao b : (t.poolSwap ci co ai ao b).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_addDelta (t : Tx) c a d : (t.addDelta c a d).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_setOrder (t : Tx) k i : (t.setOrder k i).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_createOrder (t : Tx) k i : (t.createOrder k i).w.openKeys = insert k t.w.openKeys := rfl
@[simp] theorem openKeys_deleteOrder (t : Tx) k : (t.deleteOrder k).w.openKeys = t.w.openKeys.erase k := rfl
@[simp] theorem openKeys_setPendingNative (t : Tx) n : (t.setPendingNative n).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.openKeys = t.w.openKeys := rfl
@[simp] theorem openKeys_start (w : World) : (Tx.start w).w.openKeys = w.openKeys := rfl
@[simp] theorem openKeys_payOut cfg (t : Tx) c d n b by_ : (t.payOut cfg c d n b by_).w.openKeys = t.w.openKeys := by
  unfold Tx.payOut; split_ifs <;> rfl

/-! ### `owed` and the hook's claims through the primitives and bodies -/

theorem owed_setOrder (c : Currency) (t : Tx) (k : OrderKey) (i : OrderInfo) (hk : k ∈ t.w.openKeys) :
    owed c (t.setOrder k i).w = owed c t.w - escrowOf c k (t.w.orders k) + escrowOf c k i := by
  simp only [owed, Tx.setOrder]; exact sum_update (fun x j => escrowOf c x j) _ _ _ _ hk

theorem owed_createOrder (c : Currency) (t : Tx) (k : OrderKey) (i : OrderInfo) (hk : k ∉ t.w.openKeys) :
    owed c (t.createOrder k i).w = escrowOf c k i + owed c t.w := by
  simp only [owed, Tx.createOrder]; exact sum_insert_update (fun x j => escrowOf c x j) _ _ _ _ hk

theorem owed_deleteOrder (c : Currency) (t : Tx) (k : OrderKey) (hk : k ∈ t.w.openKeys) :
    owed c (t.deleteOrder k).w = owed c t.w - escrowOf c k (t.w.orders k) := by
  simp only [owed, Tx.deleteOrder]; exact sum_erase_update (fun x j => escrowOf c x j) _ _ _ _ hk

theorem owed_payOutBody (cfg : Config) (t : Tx) c r n c' : owed c' (payOutBody cfg t c r n).w = owed c' t.w := by
  simp [owed, orders_payOutBody, openKeys_payOut, payOutBody]
theorem owed_settleBidBody (cfg : Config) (t : Tx) n c : owed c (settleBidBody cfg t n).w = owed c t.w := by
  simp only [owed, orders_settleBidBody, openKeys_settleBidBody]
theorem owed_mint (t : Tx) c d n b c' : owed c' (t.mint c d n b).w = owed c' t.w := rfl
theorem owed_burn (t : Tx) c s n b c' : owed c' (t.burn c s n b).w = owed c' t.w := rfl
theorem owed_settle cfg (t : Tx) c p d n c' : owed c' (t.settle cfg c p d n).w = owed c' t.w := rfl
theorem owed_take cfg (t : Tx) c d n b c' : owed c' (t.take cfg c d n b).w = owed c' t.w := rfl
theorem owed_transfer (t : Tx) c s d n c' : owed c' (t.transfer c s d n).w = owed c' t.w := rfl
theorem owed_accountSwap (t : Tx) c s h n c' : owed c' (t.accountSwap c s h n).w = owed c' t.w := rfl
theorem owed_addDelta (t : Tx) c a d c' : owed c' (t.addDelta c a d).w = owed c' t.w := rfl
theorem owed_poolSwap (t : Tx) ci co ai ao b c' : owed c' (t.poolSwap ci co ai ao b).w = owed c' t.w := rfl
theorem owed_setPendingNative (t : Tx) n c' : owed c' (t.setPendingNative n).w = owed c' t.w := rfl
theorem owed_useRouterCancelNonce (t : Tx) m n c' : owed c' (t.useRouterCancelNonce m n).w = owed c' t.w := rfl
theorem owed_start (w : World) c : owed c (Tx.start w).w = owed c w := rfl
theorem owed_payOut cfg (t : Tx) c d n b by_ c' : owed c' (t.payOut cfg c d n b by_).w = owed c' t.w := by
  unfold Tx.payOut; split_ifs <;> rfl

theorem claims_hook_settleBidBody (cfg : Config) (t : Tx) (n : ℕ) (c : Currency) :
    (settleBidBody cfg t n).w.claims c cfg.hook = t.w.claims c cfg.hook - (if c = numeraire then (n : ℤ) else 0) := by
  have hhv := cfg.hook_ne_vault
  simp only [settleBidBody]
  split_ifs <;> simp only [claims_mint_apply, claims_burn_apply, claims_donate] <;>
    split_ifs <;> simp_all

theorem claims_hook_payOutBody (cfg : Config) (t : Tx) (c : Currency) (r : Address) (n : ℕ)
    (hr : r ≠ cfg.hook) (c' : Currency) :
    (payOutBody cfg t c r n).w.claims c' cfg.hook = t.w.claims c' cfg.hook - (if c' = c then (n : ℤ) else 0) := by
  simp only [payOutBody, Tx.payOut]
  split_ifs <;> simp only [claims_mint_apply, claims_burn_apply, claims_take] <;>
    split_ifs <;> simp_all

theorem claims_hook_payOut (cfg : Config) (t : Tx) (c : Currency) (r : Address) (n : ℕ) (b : Bool)
    (hr : r ≠ cfg.hook) (c' : Currency) :
    (t.payOut cfg c r n b cfg.hook).w.claims c' cfg.hook = t.w.claims c' cfg.hook := by
  simp only [Tx.payOut]
  split_ifs <;> simp only [claims_mint_apply, claims_take] <;> split_ifs <;> simp_all

/-- **One matched side keeps the escrow equation**, given the leg is admissible. -/
theorem escrow_reduceSideBody (cfg : Config) (t : Tx) (k : OrderKey) (cp : Address) (used received : ℕ)
    (hk : k ∈ t.w.openKeys) (hcp : cp ≠ cfg.hook) (hown : k.owner ≠ cfg.hook)
    (hused : used ≤ (t.w.orders k).amountIn)
    (hesc : (t.w.orders k).priorityFee ≠ 0 → (t.w.orders k).escrowed = true)
    (hclaims : ∀ c, t.w.claims c cfg.hook = owed c t.w) :
    ∀ c, (reduceSideBody cfg t k cp used received).w.claims c cfg.hook
          = owed c (reduceSideBody cfg t k cp used received).w := by
  intro c
  have hesc' : (t.w.orders k).escrowed = false → (t.w.orders k).priorityFee = 0 := by
    intro h; by_contra hne; have := hesc hne; simp [h] at this
  have hc := hclaims c
  simp only [reduceSideBody]
  -- name the reduced record and the bid share, and the two accounting facts about them
  have hin : ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).amountIn + used
      = (t.w.orders k).amountIn :=
    AsyncSwap.Order.reduce_amountIn (OrderInfo.toSpec k (t.w.orders k)) ⟨used, received⟩ hused
  have hfee : ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).priorityFee
      + (OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩ = (t.w.orders k).priorityFee :=
    AsyncSwap.Order.reduce_priorityFee (OrderInfo.toSpec k (t.w.orders k)) ⟨used, received⟩ hused
  have hd : (OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩ ≤ (t.w.orders k).priorityFee :=
    AsyncSwap.mulDiv_le_of_le hused
  generalize hR : (OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩ = r at hin hfee ⊢
  generalize hF : (OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩ = fb at hfee hd ⊢
  have hmem : ∀ (t' : Tx), t'.w.openKeys = t.w.openKeys → k ∈ t'.w.openKeys := fun _ h => h ▸ hk
  cases he : (t.w.orders k).escrowed with
  | false =>
    have hf0 := hesc' he
    split_ifs with hclosed hz
    · rw [owed_deleteOrder _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, owed_settleBidBody, owed_payOutBody, hc, hf0]
      unfold escrowOf
      simp only [he, Bool.false_eq_true, ↓reduceIte, add_zero]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all
    · rw [owed_deleteOrder _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, claims_hook_payOutBody cfg _ _ _ _ hown,
        owed_settleBidBody, owed_payOutBody, hc, hf0]
      unfold escrowOf
      simp only [he, Bool.false_eq_true, ↓reduceIte, add_zero]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all
    · rw [owed_setOrder _ _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, owed_settleBidBody, owed_payOutBody, hc, hf0]
      unfold escrowOf
      simp only [he, Bool.false_eq_true, ↓reduceIte, add_zero]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all
  | true =>
    split_ifs with hclosed hz
    · rw [owed_deleteOrder _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, owed_settleBidBody, owed_payOutBody, hc]
      unfold escrowOf
      simp only [he, ↓reduceIte]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all
    · rw [owed_deleteOrder _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, claims_hook_payOutBody cfg _ _ _ _ hown,
        owed_settleBidBody, owed_payOutBody, hc]
      unfold escrowOf
      simp only [he, ↓reduceIte]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all
    · rw [owed_setOrder _ _ _ _ (hmem _ (by simp [openKeys_settleBidBody, openKeys_payOut, payOutBody]))]
      simp only [claims_deleteOrder, claims_setOrder, orders_settleBidBody, orders_payOutBody, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hcp, owed_settleBidBody, owed_payOutBody, hc]
      unfold escrowOf
      simp only [he, ↓reduceIte]
      split_ifs <;> (try subst_vars) <;> first | omega | simp_all

theorem wf_reduceSideBody (cfg : Config) (t : Tx) (k : OrderKey) (cp : Address) (used received : ℕ)
    (hwf : ∀ k' ∈ t.w.openKeys, 0 < (t.w.orders k').amountIn) :
    ∀ k' ∈ (reduceSideBody cfg t k cp used received).w.openKeys,
      0 < ((reduceSideBody cfg t k cp used received).w.orders k').amountIn := by
  intro k' hk'
  simp only [reduceSideBody] at hk' ⊢
  split_ifs at hk' ⊢ with hclosed hz
  · simp only [openKeys_deleteOrder, openKeys_settleBidBody, openKeys_payOut, payOutBody,
      openKeys_burn] at hk'
    simp only [orders_deleteOrder, orders_settleBidBody, orders_payOutBody,
      Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    exact hwf _ (Finset.mem_of_mem_erase hk')
  · simp only [openKeys_deleteOrder, openKeys_settleBidBody, openKeys_payOut, payOutBody,
      openKeys_burn] at hk'
    simp only [orders_deleteOrder, orders_settleBidBody, orders_payOutBody,
      Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    exact hwf _ (Finset.mem_of_mem_erase hk')
  · simp only [openKeys_setOrder, openKeys_settleBidBody, openKeys_payOut, payOutBody, openKeys_burn] at hk'
    simp only [orders_setOrder, orders_settleBidBody, orders_payOutBody, Function.update_apply]
    split_ifs with he
    · simp only [not_or] at hclosed; dsimp only; omega
    · exact hwf _ hk'

/-- Escrow is preserved by one admissible match. -/
theorem escrow_matchPairBody (cfg : Config) (t : Tx) (m : MatchChoice)
    (hg : matchGuard cfg t.w m.sellKey m.buyKey m.restingBuy) (hE : Escrow cfg t.w) :
    Escrow cfg (matchPairBody cfg t m.sellKey m.buyKey m.restingBuy).w := by
  obtain ⟨hsell, hbuy, hsb, hbb, hescS, hescB, _, ha, hq, hhs, hhb⟩ := hg
  have hne : m.buyKey ≠ m.sellKey := by
    intro e; rw [e, hsb] at hbb; exact Bool.false_ne_true hbb
  -- positive inputs ⇒ matchAmounts is sound ⇒ both legs fit their escrows
  have hs0 := hE.wf _ hsell
  have hb0 := hE.wf _ hbuy
  have hsound := AsyncSwap.matchAmounts_sound (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey))
    (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey)) m.restingBuy (by simpa [OrderInfo.toSpec] using hs0)
    (by simpa [OrderInfo.toSpec] using hb0) _ rfl ha hq
  have hA := hsound.asset_le_sell_escrow
  have hQ := hsound.quote_le_buy_escrow
  simp only [OrderInfo.toSpec] at hA hQ
  simp only [matchPairBody]
  set A := (AsyncSwap.matchAmounts (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey))
      (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey)) m.restingBuy).assetAmount with hAdef
  set Q := (AsyncSwap.matchAmounts (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey))
      (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey)) m.restingBuy).quoteAmount with hQdef
  -- after the sell side, the buy record and membership are unchanged
  have hbuy' : m.buyKey ∈ (reduceSideBody cfg t m.sellKey m.buyKey.owner A Q).w.openKeys := by
    simp only [reduceSideBody]; split_ifs <;>
      simp [Tx.deleteOrder, Tx.setOrder, openKeys_settleBidBody, openKeys_payOut, payOutBody, hbuy, hne]
  have hordB := orders_reduceSideBody_ne cfg t m.sellKey m.buyKey m.buyKey.owner A Q hne
  have h1 := escrow_reduceSideBody cfg t m.sellKey m.buyKey.owner A Q hsell (hE.owner_ne_hook _ hbuy)
    (hE.owner_ne_hook _ hsell) hA hescS hE.claims
  have hwf1 := wf_reduceSideBody cfg t m.sellKey m.buyKey.owner A Q hE.wf
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact escrow_reduceSideBody cfg _ m.buyKey m.sellKey.owner Q A hbuy' (hE.owner_ne_hook _ hsell)
      (hE.owner_ne_hook _ hbuy) (by rw [hordB]; exact hQ) (by rw [hordB]; exact hescB) h1
  · exact wf_reduceSideBody cfg _ m.buyKey m.sellKey.owner Q A hwf1
  · intro k hk
    exact hE.owner_ne_hook k
      (openKeys_reduceSideBody_subset cfg _ _ _ _ _ (openKeys_reduceSideBody_subset cfg _ _ _ _ _ hk))
  · intro k hk
    exact hE.owner_ne_pm k
      (openKeys_reduceSideBody_subset cfg _ _ _ _ _ (openKeys_reduceSideBody_subset cfg _ _ _ _ _ hk))

theorem escrow_matchLoop (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    Escrow cfg t.w → matchLoop cfg t ms = some t' → Escrow cfg t'.w := by
  intro ms
  induction ms with
  | nil => intro t t' hE h; simp only [matchLoop, Option.some.injEq] at h; subst h; exact hE
  | cons m ms ih =>
    intro t t' hE h
    simp only [matchLoop] at h
    split_ifs at h with hg
    exact ih _ _ (escrow_matchPairBody cfg t m hg hE) h

/-- Closing bodies (fill / cancel / liquidity fill): the order's whole escrow leaves the hook. -/
theorem escrow_closeBody (cfg : Config) (t : Tx) (o : Order) (hE : Escrow cfg t.w) (hk : o.key ∈ t.w.openKeys)
    (hesc : (t.w.orders o.key).priorityFee ≠ 0 → (t.w.orders o.key).escrowed = true)
    (t' : Tx) (hclaims : ∀ c, t'.w.claims c cfg.hook = t.w.claims c cfg.hook
        - (if c = o.input then ((t.w.orders o.key).amountIn : ℤ) else 0)
        - (if c = numeraire then ((t.w.orders o.key).priorityFee : ℤ) else 0))
    (horders : t'.w.orders = Function.update t.w.orders o.key ⟨0, 0, 0, false⟩)
    (hopen : t'.w.openKeys = t.w.openKeys.erase o.key) : Escrow cfg t'.w := by
  have hesc' : (t.w.orders o.key).escrowed = false → (t.w.orders o.key).priorityFee = 0 := by
    intro h; by_contra hne; have := hesc hne; simp [h] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    have hc := hE.claims c
    have hcl := hclaims c
    have hsum : owed c t'.w = owed c t.w - escrowOf c o.key (t.w.orders o.key) := by
      simp only [owed, horders, hopen]; exact sum_erase_update (fun x j => escrowOf c x j) _ _ _ _ hk
    rw [hcl, hsum, hc]
    unfold escrowOf
    cases he : (t.w.orders o.key).escrowed <;> (try have hf0 := hesc' he) <;>
      cases c <;> cases hz : o.zeroForOne <;>
      simp only [Order.input_eq, Order.key_input, numeraire, hz, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, sub_zero] <;>
      omega
  · intro k hk'
    rw [hopen] at hk'
    rw [horders, Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    exact hE.wf k (Finset.mem_of_mem_erase hk')
  · intro k hk'; rw [hopen] at hk'; exact hE.owner_ne_hook k (Finset.mem_of_mem_erase hk')
  · intro k hk'; rw [hopen] at hk'; exact hE.owner_ne_pm k (Finset.mem_of_mem_erase hk')

/-- **Escrow is preserved by every v2 entry point.**  Environment assumptions: makers,
    fillers and redeemers are users (never the hook or the PoolManager). -/
theorem step_escrow {cfg : Config} {w w' : World} {a : Action} (hE : Escrow cfg w)
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.hook ∧ o.owner ≠ cfg.pm)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.hook)
    (hredeem : ∀ s n r, a = .redeemNative s n r → s ≠ cfg.hook) :
    Escrow cfg w' := by
  cases a with
  | swap s o v up ms =>
    obtain ⟨hoh, hop⟩ := hswap s o v up ms rfl
    simp only [step, swap] at h
    split_ifs at h with hg
    cases hbd : swapBody cfg w s o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [swapBody] at hbd
      refine escrow_matchLoop cfg ms _ t ?_ hbd
      -- the state after create + bid escrow satisfies Escrow
      obtain ⟨_, _, _, _, _, _, _, _, hpos, _, _, hzero, _⟩ := hg.1
      have hfresh : o.key ∉ w.openKeys := fun hin => by have := hE.wf _ hin; omega
      have hrh := cfg.router_ne_hook
      have key : ∀ (t0 : Tx), Escrow cfg t0.w → t0.w.orders = w.orders → t0.w.openKeys = w.openKeys →
          ∀ payer, Escrow cfg (priorityFeeBody cfg (createBody cfg t0 o payer) o).w := by
        intro t0 hE0 ho0 hk0 payer
        have hfresh0 : o.key ∉ t0.w.openKeys := by rw [hk0]; exact hfresh
        have hfresh0' : o.key ∉ (t0.mint o.input cfg.hook o.amountIn cfg.hook).w.openKeys := hfresh0
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro c
          have hc := hE0.claims c
          simp only [priorityFeeBody]
          split_ifs with hf
          · have hdec : decide (o.priorityFee = 0) = true := by simp [hf]
            simp only [createBody, Tx.settle, Tx.accountSwap, claims_addDelta, claims_transfer,
              claims_createOrder, claims_mint_apply, owed_settle, owed_accountSwap, owed_transfer,
              owed_addDelta, owed_createOrder c _ _ _ hfresh0', owed_mint, hc, hdec, hf]
            unfold escrowOf
            cases c <;> cases hz : o.zeroForOne <;>
              simp only [Order.input_eq, Order.key_input, numeraire, hz, Bool.not_true, Bool.not_false,
                Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Nat.cast_zero, add_zero] <;> omega
          · have hdec : decide (o.priorityFee = 0) = false := by simp [hf]
            have hmem' : o.key ∈ (((createBody cfg t0 o payer).settle cfg numeraire o.owner cfg.hook o.priorityFee).mint
                numeraire cfg.hook o.priorityFee cfg.hook).w.openKeys := by simp [createBody]
            rw [owed_setOrder _ _ _ _ hmem']
            simp only [createBody, Tx.settle, Tx.accountSwap, claims_setOrder, claims_addDelta, claims_transfer,
              claims_createOrder, claims_mint_apply, orders_createOrder, orders_mint, orders_accountSwap,
              orders_addDelta, orders_transfer, Function.update_self, owed_settle,
              owed_accountSwap, owed_transfer, owed_addDelta, owed_createOrder c _ _ _ hfresh0', owed_mint,
              hc, hdec]
            unfold escrowOf
            cases c <;> cases hz : o.zeroForOne <;>
              simp only [Order.input_eq, Order.key_input, numeraire, hz, Bool.not_true, Bool.not_false,
                Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero] <;> omega
        · intro k hk
          simp only [openKeys_priorityFeeBody, openKeys_createBody, Finset.mem_insert] at hk
          simp only [priorityFeeBody]
          split_ifs <;> simp only [orders_setOrder, orders_createBody, orders_mint, orders_addDelta,
            orders_transfer, orders_settle, orders_accountSwap, Function.update_apply]
          · rcases hk with rfl | hk
            · simp [hpos]
            · (try rw [if_neg (ne_of_mem_of_not_mem hk hfresh0)]); exact hE0.wf k hk
          · split_ifs with he
            · subst he; simp [hpos]
            · rcases hk with rfl | hk
              · exact absurd rfl he
              · (try rw [if_neg he]); exact hE0.wf k hk
        · intro k hk
          simp only [openKeys_priorityFeeBody, openKeys_createBody, Finset.mem_insert] at hk
          rcases hk with rfl | hk
          · exact hoh
          · exact hE0.owner_ne_hook k hk
        · intro k hk
          simp only [openKeys_priorityFeeBody, openKeys_createBody, Finset.mem_insert] at hk
          rcases hk with rfl | hk
          · exact hop
          · exact hE0.owner_ne_pm k hk
      split_ifs
      · exact key _ ⟨fun c => hE.claims c, hE.wf, hE.owner_ne_hook, hE.owner_ne_pm⟩ rfl rfl _
      · exact key _ hE rfl rfl _
  | matchBook s mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hbd : matchLoop cfg (Tx.start w) ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      exact escrow_matchLoop cfg ms _ t hE hbd
  | fillOrder s o mp v =>
    have hs := hfill s o mp v rfl
    simp only [step, fillOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, _, _, _, hesc, hk⟩ := hg.1
    have hoh : o.owner ≠ cfg.hook := hE.owner_ne_hook _ hk
    have hhv := cfg.hook_ne_vault
    refine escrow_closeBody cfg (Tx.start w) o hE hk hesc _ ?_ ?_ ?_
    · intro c
      simp only [fillBody, claims_setPendingNative, claims_deleteOrder, claims_hook_settleBidBody,
        claims_hook_payOutBody cfg _ _ _ _ hs, claims_mint_apply, claims_hook_payOut cfg _ _ _ _ _ hoh,
        claims_settle, claims_transfer, claims_start, orders_start]
      cases c <;> cases hz : o.zeroForOne <;> by_cases hn : cfg.native0 = true <;>
        simp only [Order.input_eq, Order.output_eq, Order.key_input, Order.key_output, numeraire, hz,
          Config.isNative, hn, hhv, Ne.symm hhv, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, sub_zero,
          claims_settle, claims_transfer, claims_setPendingNative, claims_start] <;>
        (try split_ifs) <;> omega
    · simp only [fillBody, orders_setPendingNative, orders_deleteOrder, orders_settleBidBody, orders_payOutBody,
        orders_mint, orders_payOut, orders_settle, orders_transfer, orders_start]
      split_ifs <;> rfl
    · simp only [fillBody, openKeys_setPendingNative, openKeys_deleteOrder, openKeys_settleBidBody,
        openKeys_payOut, payOutBody, openKeys_burn, openKeys_mint, openKeys_settle, openKeys_transfer,
        openKeys_start]
      split_ifs <;> rfl
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, _, hesc, hk⟩ := hg.2.1
    have hoh : o.owner ≠ cfg.hook := hE.owner_ne_hook _ hk
    refine escrow_closeBody cfg (Tx.start w) o hE hk hesc _ ?_ ?_ ?_
    · intro c
      simp only [cancelBody, claims_deleteOrder, claims_hook_settleBidBody, claims_hook_payOutBody cfg _ _ _ _ hoh,
        claims_start, orders_start]
    · simp [cancelBody, orders_settleBidBody, orders_payOutBody]
    · simp [cancelBody, openKeys_settleBidBody, openKeys_payOut, payOutBody]
  | cancelWithSig s o nonce deadline now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨_, _, hesc, hk⟩ := hg.1.2.2.2
    have hoh : o.owner ≠ cfg.hook := hE.owner_ne_hook _ hk
    refine escrow_closeBody cfg (Tx.start w) o hE hk hesc _ ?_ ?_ ?_
    · intro c
      simp only [cancelBody, claims_deleteOrder, claims_hook_settleBidBody, claims_hook_payOutBody cfg _ _ _ _ hoh,
        claims_useRouterCancelNonce, claims_start, orders_useRouterCancelNonce, orders_start]
    · simp [cancelBody, orders_settleBidBody, orders_payOutBody]
    · simp [cancelBody, openKeys_settleBidBody, openKeys_payOut, payOutBody]
  | fillFromPoolLiquidity s o amountOut =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    obtain ⟨hk, _, _, _, _, hesc⟩ := hg.1
    have hoh : o.owner ≠ cfg.hook := hE.owner_ne_hook _ hk
    refine escrow_closeBody cfg (Tx.start w) o hE hk hesc _ ?_ ?_ ?_
    · intro c
      simp only [liquidityFillBody, claims_deleteOrder, claims_hook_settleBidBody,
        claims_hook_payOut cfg _ _ _ _ _ hoh, claims_poolSwap, claims_burn_apply, claims_start, orders_start]
      cases c <;> cases hz : o.zeroForOne <;>
        simp only [Order.input_eq, Order.output_eq, Order.key_input, Order.key_output, numeraire, hz,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero,
          sub_zero] <;> split_ifs <;> omega
    · simp [liquidityFillBody, orders_settleBidBody, Tx.payOut]; split_ifs <;> rfl
    · simp [liquidityFillBody, openKeys_settleBidBody, Tx.payOut]; split_ifs <;> rfl
  | redeemNative s n r =>
    have hs := hredeem s n r rfl
    simp only [step, redeemNative] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, hE.wf, hE.owner_ne_hook, hE.owner_ne_pm⟩
    intro c
    simp only [Tx.take, claims_addDelta, claims_transfer, claims_burn_apply, owed_addDelta, owed_transfer,
      owed_burn, owed_start, claims_start, Ne.symm hs, ↓reduceIte]
    split_ifs <;> (try subst_vars) <;> exact hE.claims _
  | updatePrice s o m =>
    simp only [step, updatePrice] at h
    split_ifs at h with hg; simp only [Option.some.injEq] at h; subst h
    refine ⟨?_, ?_, hE.owner_ne_hook, hE.owner_ne_pm⟩
    · intro c
      have hk : o.key ∈ w.openKeys := hg.2.2.2
      rw [owed_setOrder _ _ _ _ hk]
      simp only [claims_setOrder, claims_start, orders_start, owed_start, hE.claims c]
      unfold escrowOf
      (try dsimp only)
      split_ifs <;> omega
    · intro k hk
      simp only [Tx.setOrder, Function.update_apply]
      split_ifs with he
      · subst he; exact hE.wf _ hk
      · exact hE.wf _ hk
  | setOrderingMode s mode =>
    simp only [step, setOrderingMode] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact ⟨fun c => hE.claims c, hE.wf, hE.owner_ne_hook, hE.owner_ne_pm⟩
  | setExecutor s e al =>
    simp only [step, Protocol.setExecutor, Option.some.injEq] at h; subst h
    exact ⟨fun c => hE.claims c, hE.wf, hE.owner_ne_hook, hE.owner_ne_pm⟩

end AsyncSwapProtocol.V2
