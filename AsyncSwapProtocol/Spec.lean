import AsyncSwapProtocol.Model

/-!
# Protocol specification — part 1: lifecycle, settlement, authorization

Theorems about `Protocol.step` (`Model.lean`).  Part 2 (`Invariants.lean`) covers
conservation and the escrow / claims-backing invariants.
-/

namespace AsyncSwapProtocol
open Protocol Tx

/-! ## Order lifecycle: the README state diagram -/

inductive OrderState
  | absent
  | open_
  deriving DecidableEq, Repr

/-- `Absent: no open order record` / `Open: amountIn > 0`. -/
def orderState (w : World) (k : OrderKey) : OrderState :=
  if (w.orders k).amountIn = 0 then .absent else .open_

@[simp] theorem Order.input_eq_output_iff (o : Order) : (o.input = o.output) ↔ False :=
  ⟨fun h => o.input_ne_output h, False.elim⟩
@[simp] theorem Order.output_eq_input_iff (o : Order) : (o.output = o.input) ↔ False :=
  ⟨fun h => o.input_ne_output h.symm, False.elim⟩

/-- Bookkeeping primitives do not touch order storage. -/
@[simp] theorem orders_transfer (t : Tx) c s d n : (t.transfer c s d n).w.orders = t.w.orders := rfl
@[simp] theorem orders_mint (t : Tx) c d n b : (t.mint c d n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_burn (t : Tx) c s n b : (t.burn c s n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.orders = t.w.orders := rfl
@[simp] theorem orders_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.orders = t.w.orders := rfl
@[simp] theorem orders_addDelta (t : Tx) c a d : (t.addDelta c a d).w.orders = t.w.orders := rfl
@[simp] theorem orders_setExecutor (t : Tx) m e a : (t.setExecutor m e a).w.orders = t.w.orders := rfl
@[simp] theorem orders_useHookNonce (t : Tx) m n : (t.useHookNonce m n).w.orders = t.w.orders := rfl
@[simp] theorem orders_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.orders = t.w.orders := rfl
@[simp] theorem orders_usePermit2Nonce (t : Tx) m n : (t.usePermit2Nonce m n).w.orders = t.w.orders := rfl
@[simp] theorem orders_setPendingNative (t : Tx) n : (t.setPendingNative n).w.orders = t.w.orders := rfl
@[simp] theorem orders_start (w : World) : (Tx.start w).w.orders = w.orders := rfl
@[simp] theorem orders_createOrder (t : Tx) k i : (t.createOrder k i).w.orders = Function.update t.w.orders k i := rfl
@[simp] theorem orders_deleteOrder (t : Tx) k : (t.deleteOrder k).w.orders = Function.update t.w.orders k ⟨0, 0⟩ := rfl
@[simp] theorem orders_setMinimum (t : Tx) k m :
    (t.setMinimum k m).w.orders = Function.update t.w.orders k ⟨(t.w.orders k).amountIn, m⟩ := rfl

theorem orders_createBody (cfg : Config) (t : Tx) (o : Order) (info : OrderInfo) (payer : Address) :
    (createBody cfg t o info payer).w.orders = Function.update t.w.orders o.key info := by
  simp [createBody]

theorem orders_swapBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) :
    (swapBody cfg w sender o value).w.orders = Function.update w.orders o.key ⟨o.amountIn, o.amountOutMin⟩ := by
  unfold swapBody; split_ifs <;> simp [orders_createBody]

theorem orders_swapWithSigBody (cfg : Config) (w : World) (o : Order) (p : PermitData) (g : ExecutorGrant) :
    (swapWithSigBody cfg w o p g).w.orders = Function.update w.orders o.key ⟨o.amountIn, o.amountOutMin⟩ := by
  unfold swapWithSigBody; split_ifs <;> simp [orders_createBody]

theorem orders_fillBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) :
    (fillBody cfg w sender o value).w.orders = Function.update w.orders o.key ⟨0, 0⟩ := by
  simp only [fillBody]; split_ifs <;> simp

theorem orders_cancelBody (cfg : Config) (t : Tx) (o : Order) :
    (cancelBody cfg t o).w.orders = Function.update t.w.orders o.key ⟨0, 0⟩ := by
  simp [cancelBody]

theorem orders_collectBody (cfg : Config) (w : World) (c : Currency) (r : Address) :
    (collectBody cfg w c r).w.orders = w.orders := by
  simp only [collectBody]; split_ifs <;> simp

/-- **Frame.** No action changes any order record other than the one it names. -/
theorem step_frame {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    {k : OrderKey} (hk : a.key ≠ some k) : w'.orders k = w.orders k := by
  cases a <;> simp only [step, Action.key, ne_eq, Option.some.injEq] at h hk <;>
    simp only [swap, swapWithSig, fillOrder, cancelOrder, cancelWithSig, updatePrice,
      updatePriceWithSig, Protocol.setExecutor, setExecutorWithSig, invalidateNonce, collectFees,
      transferOwnership, acceptOwnership, sweep] at h <;>
    (try split_ifs at h) <;> simp only [Option.some.injEq] at h <;> subst h <;>
    simp [orders_swapBody, orders_swapWithSigBody, orders_fillBody, orders_cancelBody,
      cancelWithSigBody, orders_collectBody, Function.update_of_ne (Ne.symm hk)]

/-- **T0 Create.** A successful `swap` / `swapWithSig` opens exactly the named order with
    positive amounts, and the slot was absent before. -/
theorem create_effect {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    (hc : a.isCreate = true) {k : OrderKey} (hk : a.key = some k) :
    (w.orders k).amountIn = 0 ∧
      ∃ amountIn amountOutMin : ℕ, w'.orders k = ⟨amountIn, amountOutMin⟩
        ∧ 0 < amountIn ∧ 0 < amountOutMin := by
  cases a <;> simp only [Action.isCreate, Bool.false_eq_true] at hc
  · simp only [step, swap, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    obtain ⟨⟨_, _, _, hmin, _, _, hpos, _, hmin', hfresh⟩, _⟩ := hg
    refine ⟨hfresh, _, _, ?_, hpos, hmin ▸ hmin'⟩
    rw [orders_swapBody, Function.update_self]
  · simp only [step, swapWithSig, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    obtain ⟨⟨_, _, _, hpos, hmin, hfresh, _⟩, _⟩ := hg
    refine ⟨hfresh, _, _, ?_, hpos, hmin⟩
    rw [orders_swapWithSigBody, Function.update_self]

/-- **T2 / T3 Fill, Cancel.** A successful close deletes exactly the named order, which was
    open before. -/
theorem close_effect {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    (hc : a.isClose = true) {k : OrderKey} (hk : a.key = some k) :
    (w.orders k).amountIn ≠ 0 ∧ w'.orders k = ⟨0, 0⟩ := by
  cases a <;> simp only [Action.isClose, Bool.false_eq_true] at hc
  · simp only [step, fillOrder, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    refine ⟨hg.1.2.2.2.1, ?_⟩
    rw [orders_fillBody, Function.update_self]
  · simp only [step, cancelOrder, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    refine ⟨hg.2.1.2.1, ?_⟩
    rw [orders_cancelBody, orders_start, Function.update_self]
  · simp only [step, cancelWithSig, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    refine ⟨hg.1.2.2.2.2.1, ?_⟩
    simp only [cancelWithSigBody, orders_cancelBody, orders_useRouterCancelNonce, orders_start,
      Function.update_self]

/-- **T1 Reprice.** A successful reprice keeps the escrow and replaces only the minimum. -/
theorem reprice_effect {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    (hr : a.isReprice = true) {k : OrderKey} (hk : a.key = some k) :
    (w.orders k).amountIn ≠ 0 ∧ (w'.orders k).amountIn = (w.orders k).amountIn
      ∧ (w'.orders k).amountOutMin ≠ 0 := by
  cases a <;> simp only [Action.isReprice, Bool.false_eq_true] at hr
  · simp only [step, updatePrice, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    obtain ⟨_, hmin, hopen⟩ := hg
    simp [Function.update_self, hopen, hmin]
  · simp only [step, updatePriceWithSig, Action.key, Option.some.injEq] at h hk
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h; subst hk
    obtain ⟨_, _, _, _, hmin, hopen⟩ := hg
    simp [Function.update_self, hopen, hmin]

theorem Action.key_cases (a : Action) (k : OrderKey) (h : a.key = some k) :
    a.isCreate = true ∨ a.isClose = true ∨ a.isReprice = true := by
  cases a <;> simp_all [Action.key, Action.isCreate, Action.isClose, Action.isReprice]

/-- **Lifecycle.** The only transitions are `Absent → Open` by a create of that key,
    `Open → Absent` by a close of that key, and `Open → Open` (reprice).  Every other action
    leaves every order state unchanged. -/
theorem step_lifecycle {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    (k : OrderKey) :
    (orderState w k = .absent →
       orderState w' k = .absent ∨ (a.isCreate = true ∧ a.key = some k)) ∧
    (orderState w k = .open_ →
       orderState w' k = .open_ ∨ (a.isClose = true ∧ a.key = some k)) := by
  by_cases hk : a.key = some k
  · rcases Action.key_cases a k hk with hc | hc | hc
    · obtain ⟨habs, _, _, _, _, _⟩ := create_effect h hc hk
      refine ⟨fun _ => Or.inr ⟨hc, hk⟩, fun hopen => ?_⟩
      simp [orderState, habs] at hopen
    · obtain ⟨hopen, _⟩ := close_effect h hc hk
      refine ⟨fun habs => ?_, fun _ => Or.inr ⟨hc, hk⟩⟩
      simp [orderState, hopen] at habs
    · obtain ⟨hopen, heq, _⟩ := reprice_effect h hc hk
      refine ⟨fun habs => ?_, fun _ => Or.inl ?_⟩
      · simp [orderState, hopen] at habs
      · simp [orderState, heq, hopen]
  · have := step_frame h hk
    simp only [orderState, this]
    exact ⟨fun h => Or.inl h, fun h => Or.inl h⟩

end AsyncSwapProtocol
