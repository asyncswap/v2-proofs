import AsyncSwapProtocol.Spec

/-!
# Protocol specification — part 2: settlement, delta neutrality, authorization

What each successful transaction pays to whom, read off `Protocol.step`.
-/

namespace AsyncSwapProtocol
open Protocol Tx

/-! ## Evaluation lemmas for the primitives -/

@[simp] theorem bal_start (w : World) : (Tx.start w).w.bal = w.bal := rfl
@[simp] theorem claims_start (w : World) : (Tx.start w).w.claims = w.claims := rfl
@[simp] theorem delta_start (w : World) : (Tx.start w).delta = fun _ _ => 0 := rfl

@[simp] theorem bal_mint (t : Tx) c d n b : (t.mint c d n b).w.bal = t.w.bal := rfl
@[simp] theorem bal_burn (t : Tx) c s n b : (t.burn c s n b).w.bal = t.w.bal := rfl
@[simp] theorem bal_addDelta (t : Tx) c a d : (t.addDelta c a d).w.bal = t.w.bal := rfl
@[simp] theorem bal_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.bal = t.w.bal := rfl
@[simp] theorem bal_createOrder (t : Tx) k i : (t.createOrder k i).w.bal = t.w.bal := rfl
@[simp] theorem bal_deleteOrder (t : Tx) k : (t.deleteOrder k).w.bal = t.w.bal := rfl
@[simp] theorem bal_setMinimum (t : Tx) k m : (t.setMinimum k m).w.bal = t.w.bal := rfl
@[simp] theorem bal_setExecutor (t : Tx) m e a : (t.setExecutor m e a).w.bal = t.w.bal := rfl
@[simp] theorem bal_useHookNonce (t : Tx) m n : (t.useHookNonce m n).w.bal = t.w.bal := rfl
@[simp] theorem bal_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.bal = t.w.bal := rfl
@[simp] theorem bal_usePermit2Nonce (t : Tx) m n : (t.usePermit2Nonce m n).w.bal = t.w.bal := rfl
@[simp] theorem bal_setPendingNative (t : Tx) n : (t.setPendingNative n).w.bal = t.w.bal := rfl

@[simp] theorem claims_transfer (t : Tx) c s d n : (t.transfer c s d n).w.claims = t.w.claims := rfl
@[simp] theorem claims_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.claims = t.w.claims := rfl
@[simp] theorem claims_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.claims = t.w.claims := rfl
@[simp] theorem claims_addDelta (t : Tx) c a d : (t.addDelta c a d).w.claims = t.w.claims := rfl
@[simp] theorem claims_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.claims = t.w.claims := rfl
@[simp] theorem claims_createOrder (t : Tx) k i : (t.createOrder k i).w.claims = t.w.claims := rfl
@[simp] theorem claims_deleteOrder (t : Tx) k : (t.deleteOrder k).w.claims = t.w.claims := rfl
@[simp] theorem claims_setMinimum (t : Tx) k m : (t.setMinimum k m).w.claims = t.w.claims := rfl
@[simp] theorem claims_setExecutor (t : Tx) m e a : (t.setExecutor m e a).w.claims = t.w.claims := rfl
@[simp] theorem claims_useHookNonce (t : Tx) m n : (t.useHookNonce m n).w.claims = t.w.claims := rfl
@[simp] theorem claims_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.claims = t.w.claims := rfl
@[simp] theorem claims_usePermit2Nonce (t : Tx) m n : (t.usePermit2Nonce m n).w.claims = t.w.claims := rfl
@[simp] theorem claims_setPendingNative (t : Tx) n : (t.setPendingNative n).w.claims = t.w.claims := rfl

@[simp] theorem delta_transfer (t : Tx) c s d n : (t.transfer c s d n).delta = t.delta := rfl
@[simp] theorem delta_createOrder (t : Tx) k i : (t.createOrder k i).delta = t.delta := rfl
@[simp] theorem delta_deleteOrder (t : Tx) k : (t.deleteOrder k).delta = t.delta := rfl
@[simp] theorem delta_setMinimum (t : Tx) k m : (t.setMinimum k m).delta = t.delta := rfl
@[simp] theorem delta_setExecutor (t : Tx) m e a : (t.setExecutor m e a).delta = t.delta := rfl
@[simp] theorem delta_useHookNonce (t : Tx) m n : (t.useHookNonce m n).delta = t.delta := rfl
@[simp] theorem delta_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).delta = t.delta := rfl
@[simp] theorem delta_usePermit2Nonce (t : Tx) m n : (t.usePermit2Nonce m n).delta = t.delta := rfl
@[simp] theorem delta_setPendingNative (t : Tx) n : (t.setPendingNative n).delta = t.delta := rfl
@[simp] theorem delta_mint (t : Tx) c d n b : (t.mint c d n b).delta = (t.addDelta c b (-(n : ℤ))).delta := rfl
@[simp] theorem delta_burn (t : Tx) c s n b : (t.burn c s n b).delta = (t.addDelta c b (n : ℤ)).delta := rfl

theorem bal_transfer_apply (t : Tx) (c : Currency) (s d : Address) (n : ℕ) (c' : Currency) (x : Address) :
    (t.transfer c s d n).w.bal c' x =
      if c' = c then
        (if x = d then (if d = s then t.w.bal c s - n else t.w.bal c d) + n
         else if x = s then t.w.bal c s - n else t.w.bal c x)
      else t.w.bal c' x := by
  simp only [Tx.transfer, Tx.debit, Tx.credit, adjust, Function.update_apply]
  split_ifs <;> simp_all

theorem delta_addDelta_apply (t : Tx) (c : Currency) (a : Address) (d : ℤ) (c' : Currency) (x : Address) :
    (t.addDelta c a d).delta c' x = if c' = c ∧ x = a then t.delta c a + d else t.delta c' x := by
  simp only [Tx.addDelta, adjust, Function.update_apply]
  split_ifs <;> simp_all

theorem claims_mint_apply (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (b : Address) (c' : Currency) (x : Address) :
    (t.mint c dst n b).w.claims c' x = if c' = c ∧ x = dst then t.w.claims c dst + n else t.w.claims c' x := by
  simp only [Tx.mint, adjust, Function.update_apply]
  split_ifs <;> simp_all

theorem claims_burn_apply (t : Tx) (c : Currency) (src : Address) (n : ℕ) (b : Address) (c' : Currency) (x : Address) :
    (t.burn c src n b).w.claims c' x = if c' = c ∧ x = src then t.w.claims c src - n else t.w.claims c' x := by
  simp only [Tx.burn, adjust, Function.update_apply]
  split_ifs <;> simp_all

/-! ## Every unlock branch leaves the PoolManager deltas net-zero -/

theorem createBody_deltasZero (cfg : Config) (t : Tx) (o : Order) (info : OrderInfo) (payer : Address)
    (ht : t.deltasZero cfg) : (createBody cfg t o info payer).deltasZero cfg := by
  intro c
  have := ht c
  simp only [createBody, Tx.settle, Tx.accountSwap, Tx.mint, delta_transfer, delta_createOrder,
    delta_addDelta_apply]
  have hrh := cfg.router_ne_hook
  have hrv := cfg.router_ne_vault
  have hhv := cfg.hook_ne_vault
  by_cases hc : c = o.input
  · subst hc; simp [hrh, hrv, hhv, Ne.symm hrh, Ne.symm hrv, Ne.symm hhv]; omega
  · simp [hc]; exact this

theorem start_deltasZero (cfg : Config) (w : World) : (Tx.start w).deltasZero cfg := by
  intro c; simp

theorem swapBody_deltasZero (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) :
    (swapBody cfg w sender o value).deltasZero cfg := by
  simp only [swapBody]
  split_ifs <;> apply createBody_deltasZero <;> intro c <;> simp

theorem swapWithSigBody_deltasZero (cfg : Config) (w : World) (o : Order) (p : PermitData) (g : ExecutorGrant) :
    (swapWithSigBody cfg w o p g).deltasZero cfg := by
  simp only [swapWithSigBody]
  split_ifs <;> apply createBody_deltasZero <;> intro c <;> simp

theorem fillBody_deltasZero (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) :
    (fillBody cfg w sender o value).deltasZero cfg := by
  intro c
  have hrh := cfg.router_ne_hook
  have hrv := cfg.router_ne_vault
  have hhv := cfg.hook_ne_vault
  have hlive : (liveGross w o.key : ℤ) = (w.orders o.key).amountOutMin + poolFee (w.orders o.key).amountOutMin := by
    simp [liveGross, gross]
  cases c <;> cases hz : o.zeroForOne <;> by_cases hn : cfg.native0 = true <;>
    simp only [fillBody, Tx.take, Tx.settle, Tx.mint, Tx.burn, Config.isNative, Order.input, Order.output,
      hz, hn, Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_eq_true,
      Bool.true_eq_false, delta_setPendingNative, delta_transfer, delta_deleteOrder, delta_start,
      delta_addDelta_apply, hrh, hrv, hhv, Ne.symm hrh, Ne.symm hrv, Ne.symm hhv, and_true, and_false,
      true_and, false_and, ↓reduceIte, eq_self_iff_true, not_false_eq_true] <;>
    omega

theorem cancelBody_deltasZero (cfg : Config) (t : Tx) (o : Order) (ht : t.deltasZero cfg) :
    (cancelBody cfg t o).deltasZero cfg := by
  intro c
  have := ht c
  have hrh := cfg.router_ne_hook
  have hhv := cfg.hook_ne_vault
  simp only [cancelBody, Tx.take, Tx.burn, delta_transfer, delta_deleteOrder, delta_addDelta_apply]
  by_cases hc : c = o.input
  · subst hc; simp [hrh, hhv, Ne.symm hrh, Ne.symm hhv]; omega
  · simp [hc]; exact this

theorem collectBody_deltasZero (cfg : Config) (w : World) (c : Currency) (r : Address) :
    (collectBody cfg w c r).deltasZero cfg := by
  intro c'
  have hrv := cfg.router_ne_vault
  have hhv := cfg.hook_ne_vault
  simp only [collectBody, Tx.take, Tx.burn, delta_transfer, delta_addDelta_apply, delta_start]
  by_cases hc : c' = c
  · subst hc; simp [hrv, hhv, Ne.symm hrv, Ne.symm hhv]
  · simp [hc]

/-- **Completeness.** The PoolManager's end-of-unlock check never reverts a transaction
    whose contract-level checks passed: `step` succeeds exactly when the guards hold. -/
theorem fillOrder_eq_some_iff (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) :
    (∃ w', fillOrder cfg w sender o maxPrice value = some w') ↔ fillGuard cfg w sender o maxPrice value := by
  simp [fillOrder, fillBody_deltasZero]

theorem swap_eq_some_iff (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) (up : UserParams) :
    (∃ w', swap cfg w sender o value up = some w') ↔ swapGuard cfg w sender o value up := by
  simp [swap, swapBody_deltasZero]

theorem cancelOrder_eq_some_iff (cfg : Config) (w : World) (sender : Address) (o : Order) :
    (∃ w', cancelOrder cfg w sender o = some w') ↔ sender = o.owner ∧ cancelHookGuard cfg w o := by
  simp [cancelOrder, cancelBody_deltasZero cfg (Tx.start w) o (start_deltasZero cfg w)]

/-! ## Fill settlement -/

/-- Addresses that must be distinct for the per-party accounting to be stated. -/
structure FillParties (cfg : Config) (sender owner : Address) : Prop where
  sender_ne_owner : sender ≠ owner
  sender_ne_pm : sender ≠ cfg.pm
  sender_ne_hook : sender ≠ cfg.hook
  sender_ne_vault : sender ≠ cfg.vault
  owner_ne_pm : owner ≠ cfg.pm
  owner_ne_hook : owner ≠ cfg.hook
  owner_ne_vault : owner ≠ cfg.vault

set_option maxHeartbeats 1000000 in
/-- **Fill pays exactly the live terms.**  The maker receives the *stored* minimum, the vault
    receives the fee on it, the filler pays live gross output and receives the whole escrow,
    and the hook's own token balances are untouched (a native fill passes the filler's deposit
    straight through: stranded ETH on the hook is never spent). -/
theorem fill_settlement {cfg : Config} {w w' : World} {sender : Address} {o : Order} {maxPrice value : ℕ}
    (h : fillOrder cfg w sender o maxPrice value = some w') (hp : FillParties cfg sender o.owner) :
    w'.bal o.output o.owner = w.bal o.output o.owner + (w.orders o.key).amountOutMin
    ∧ w'.bal o.output sender = w.bal o.output sender - liveGross w o.key
    ∧ w'.bal o.input sender = w.bal o.input sender + (w.orders o.key).amountIn
    ∧ w'.bal o.input o.owner = w.bal o.input o.owner
    ∧ w'.claims o.output cfg.vault = w.claims o.output cfg.vault + poolFee (w.orders o.key).amountOutMin
    ∧ w'.claims o.input cfg.hook = w.claims o.input cfg.hook - (w.orders o.key).amountIn
    ∧ (∀ c, w'.bal c cfg.hook = w.bal c cfg.hook)
    ∧ liveGross w o.key ≤ maxPrice := by
  unfold fillOrder at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  obtain ⟨⟨hval, hmax, _⟩, _⟩ := hg
  have hpm_hook := cfg.hook_ne_pm
  have hhv := cfg.hook_ne_vault
  have hpv := cfg.vault_ne_pm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  have hlive : (liveGross w o.key : ℤ) = (w.orders o.key).amountOutMin + poolFee (w.orders o.key).amountOutMin := by
    simp [liveGross, gross]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hmax⟩
  all_goals (try intro c)
  all_goals
    (try cases c) <;> cases hz : o.zeroForOne <;> by_cases hn : cfg.native0 = true <;>
    simp only [Config.isNative, Order.output, hz, hn, Bool.not_true, Bool.not_false, Bool.false_and,
      Bool.true_and, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hval <;>
    simp only [fillBody, Tx.take, Tx.settle, Config.isNative, Order.input, Order.output, hz, hn,
      Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.false_eq_true, Bool.true_eq_false,
      bal_setPendingNative, bal_mint, bal_burn, bal_addDelta, bal_deleteOrder, bal_start,
      claims_setPendingNative, claims_transfer, claims_addDelta, claims_deleteOrder, claims_start,
      bal_transfer_apply, claims_mint_apply, claims_burn_apply,
      h1, h2, h3, h4, h5, h6, h7, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
      Ne.symm h7, hpm_hook, hhv, hpv, Ne.symm hpm_hook, Ne.symm hhv, Ne.symm hpv,
      and_true, and_false, true_and, false_and, ↓reduceIte, eq_self_iff_true,
      not_false_eq_true] <;>
    omega

/-- A fill reads the live stored terms: the `amountIn` / `amountOutMin` the filler passes in
    calldata are irrelevant (`updatePrice` front-running cannot change what is paid beyond the
    `maxPrice` cap, and a stale struct cannot underpay the maker). -/
theorem fillOrder_ignores_calldata_amounts (cfg : Config) (w : World) (sender : Address) (o : Order)
    (maxPrice value a m : ℕ) :
    fillOrder cfg w sender { o with amountIn := a, amountOutMin := m } maxPrice value
      = fillOrder cfg w sender o maxPrice value := rfl

/-! ## Cancel settlement -/

theorem cancel_settlement {cfg : Config} {w w' : World} {sender : Address} {o : Order}
    (h : cancelOrder cfg w sender o = some w') (h1 : o.owner ≠ cfg.pm) (h2 : o.owner ≠ cfg.hook) :
    w'.bal o.input o.owner = w.bal o.input o.owner + (w.orders o.key).amountIn
    ∧ w'.claims o.input cfg.hook = w.claims o.input cfg.hook - (w.orders o.key).amountIn
    ∧ (∀ c, w'.bal c cfg.hook = w.bal c cfg.hook) := by
  unfold cancelOrder at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  have hpm_hook := cfg.hook_ne_pm
  refine ⟨?_, ?_, ?_⟩
  all_goals (try intro c)
  all_goals
    (try cases c) <;> cases hz : o.zeroForOne <;>
    simp only [cancelBody, Tx.take, Order.input, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, orders_start, bal_burn, bal_addDelta, bal_deleteOrder, bal_start,
      claims_transfer, claims_addDelta, claims_deleteOrder, claims_start, bal_transfer_apply,
      claims_burn_apply,
      h1, h2, Ne.symm h1, Ne.symm h2, hpm_hook, Ne.symm hpm_hook,
      and_true, and_false, true_and, false_and, ↓reduceIte, eq_self_iff_true,
      not_false_eq_true] <;>
    omega

/-! ## Authorization -/

theorem fill_requires_grant {cfg : Config} {w w' : World} {sender : Address} {o : Order} {maxPrice value : ℕ}
    (h : fillOrder cfg w sender o maxPrice value = some w') : w.isExecutor o.owner cfg.router = true := by
  unfold fillOrder at h; split_ifs at h with hg; exact hg.1.2.2.1

theorem fill_native_requires_exact_value {cfg : Config} {w w' : World} {sender : Address} {o : Order}
    {maxPrice value : ℕ} (h : fillOrder cfg w sender o maxPrice value = some w')
    (hn : cfg.isNative o.output = true) : value = liveGross w o.key := by
  unfold fillOrder at h; split_ifs at h with hg
  have := hg.1.1; simp [hn] at this; exact this.1

theorem cancel_requires_owner_and_grant {cfg : Config} {w w' : World} {sender : Address} {o : Order}
    (h : cancelOrder cfg w sender o = some w') :
    sender = o.owner ∧ (cfg.router = o.owner ∨ w.isExecutor o.owner cfg.router = true) := by
  unfold cancelOrder at h; split_ifs at h with hg; exact ⟨hg.1, hg.2.1.1⟩

theorem updatePrice_requires_owner {w w' : World} {sender : Address} {o : Order} {m : ℕ}
    (h : updatePrice w sender o m = some w') : sender = o.owner := by
  unfold updatePrice at h; split_ifs at h with hg; exact hg.1

/-- A signed cancel is bound to the maker, the order id and the *stored* input amount, and
    burns its nonce: replaying it is impossible. -/
theorem cancelWithSig_requires_sig {cfg : Config} {w w' : World} {o : Order} {nonce deadline now : ℕ}
    (h : cancelWithSig cfg w o nonce deadline now = some w') :
    now ≤ deadline ∧ w.routerCancelNonce o.owner nonce = false
    ∧ cfg.sigOk (.cancel o.key (w.orders o.key).amountIn nonce deadline) o.owner = true
    ∧ w'.routerCancelNonce o.owner nonce = true := by
  unfold cancelWithSig at h; split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  refine ⟨hg.1.1, hg.1.2.1, hg.1.2.2.1, ?_⟩
  simp [cancelWithSigBody, cancelBody, Tx.take, Tx.transfer, Tx.debit, Tx.credit, Tx.addDelta, Tx.burn,
    Tx.deleteOrder, Tx.useRouterCancelNonce, Tx.start]

theorem cancelWithSig_no_replay {cfg : Config} {w w' : World} {o : Order} {nonce deadline now : ℕ}
    (h : cancelWithSig cfg w o nonce deadline now = some w') (deadline' now' : ℕ) :
    cancelWithSig cfg w' o nonce deadline' now' = none := by
  have hused := (cancelWithSig_requires_sig h).2.2.2
  unfold cancelWithSig
  split_ifs with hg
  · exact absurd hg.1.2.1 (by simp [hused])
  · rfl

theorem updatePriceWithSig_requires_sig {cfg : Config} {w w' : World} {o : Order} {m nonce deadline now : ℕ}
    (h : updatePriceWithSig cfg w o m nonce deadline now = some w') :
    now ≤ deadline ∧ w.hookNonce o.owner nonce = false
    ∧ cfg.sigOk (.updatePrice o.key (w.orders o.key).amountIn m nonce deadline) o.owner = true
    ∧ w'.hookNonce o.owner nonce = true := by
  unfold updatePriceWithSig at h; split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  exact ⟨hg.1, hg.2.1, hg.2.2.1, by simp [Tx.setMinimum, Tx.useHookNonce, Tx.start]⟩

theorem nonce_update_mono' (g : ℕ → Bool) (n : ℕ) {k : ℕ} (h : g k = true) :
    Function.update g n true k = true := by
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk, h]

theorem nonce_update_mono (f : Address → ℕ → Bool) (a : Address) (n : ℕ) {m : Address} {k : ℕ}
    (h : f m k = true) : Function.update f a (Function.update (f a) n true) m k = true := by
  by_cases hm : m = a
  · subst hm; simp [nonce_update_mono' _ _ h]
  · simp [hm, h]

/-- Nonce monotonicity across the whole protocol: a used hook nonce stays used. -/
theorem step_hookNonce_mono {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w')
    {maker : Address} {n : ℕ} (hu : w.hookNonce maker n = true) : w'.hookNonce maker n = true := by
  cases a <;> simp only [step] at h <;>
    simp only [swap, swapWithSig, fillOrder, cancelOrder, cancelWithSig, updatePrice,
      updatePriceWithSig, Protocol.setExecutor, setExecutorWithSig, invalidateNonce, collectFees,
      transferOwnership, acceptOwnership, sweep] at h <;>
    (try split_ifs at h) <;> simp only [Option.some.injEq] at h <;> subst h <;>
    simp [swapBody, swapWithSigBody, createBody, fillBody, cancelBody, cancelWithSigBody, collectBody,
      Tx.take, Tx.settle, Tx.transfer, Tx.debit, Tx.credit, Tx.addDelta, Tx.mint, Tx.burn, Tx.accountSwap,
      Tx.createOrder, Tx.deleteOrder, Tx.setMinimum, Tx.setExecutor, Tx.useHookNonce,
      Tx.useRouterCancelNonce, Tx.usePermit2Nonce, Tx.setPendingNative, Tx.start,
      Function.update_apply] <;>
    (try split_ifs) <;> simp_all [nonce_update_mono, nonce_update_mono']

end AsyncSwapProtocol

namespace AsyncSwapProtocol
open Protocol Tx

/-! ## FeeVault.collect and sweep (decision 4) -/

/-- Only the current owner can collect, and collection moves exactly the vault's fee claims
    for that currency to the recipient: the vault's claims drop to zero, the recipient receives
    that amount of real tokens, and no order record or hook claim is touched. -/
theorem collect_settlement {cfg : Config} {w w' : World} {sender : Address} {c : Currency}
    {recipient : Address} (h : collectFees cfg w sender c recipient = some w')
    (hr : recipient ≠ cfg.pm) (hnn : 0 ≤ w.claims c cfg.vault) :
    sender = w.owner
    ∧ w'.claims c cfg.vault = 0
    ∧ w'.bal c recipient = w.bal c recipient + (w.claims c cfg.vault).toNat
    ∧ (∀ c', w'.claims c' cfg.hook = w.claims c' cfg.hook)
    ∧ w'.orders = w.orders := by
  unfold collectFees at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  obtain ⟨hs, _, hbacked, _⟩ := hg
  have hhv := cfg.hook_ne_vault
  have hpv := cfg.vault_ne_pm
  refine ⟨hs, ?_, ?_, ?_, by simp [orders_collectBody]⟩
  · simp only [collectBody, Tx.take, claims_transfer, claims_addDelta, claims_burn_apply, claims_start]
    simp only [true_and, ↓reduceIte]
    omega
  · cases c <;>
      simp only [collectBody, Tx.take, bal_addDelta, bal_burn, bal_transfer_apply, bal_start,
        hr, Ne.symm hr, Ne.symm hpv, hpv, and_true, and_false, true_and, false_and, ↓reduceIte,
        eq_self_iff_true, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false] <;> omega
  · intro c'
    cases c <;> cases c' <;>
      simp only [collectBody, Tx.take, claims_transfer, claims_addDelta, claims_burn_apply, claims_start,
        hhv, Ne.symm hhv, and_true, and_false, true_and, false_and, ↓reduceIte, eq_self_iff_true,
        not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false]

/-- Collecting never moves maker escrow: the hook's claims are untouched (above) and the
    PoolManager pays out at most what the vault held, which the guard requires to be backed. -/
theorem collect_requires_owner {cfg : Config} {w w' : World} {sender : Address} {c : Currency}
    {recipient : Address} (h : collectFees cfg w sender c recipient = some w') : sender = w.owner := by
  unfold collectFees at h; split_ifs at h with hg; exact hg.1

/-- `sweep` is owner-only and moves only the hook's *own* token balance: claims (escrow and
    fees) and order records are untouched, so stranded funds can be recovered but escrow cannot
    be swept. -/
theorem sweep_settlement {cfg : Config} {w w' : World} {sender : Address} {c : Currency} {dst : Address}
    (h : sweep cfg w sender c dst = some w') (hd : dst ≠ cfg.hook) :
    sender = w.owner
    ∧ w'.bal c cfg.hook = w.bal c cfg.hook - (w.bal c cfg.hook).toNat
    ∧ w'.bal c dst = w.bal c dst + (w.bal c cfg.hook).toNat
    ∧ w'.claims = w.claims
    ∧ w'.orders = w.orders := by
  unfold sweep at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  refine ⟨hg.1, ?_, ?_, rfl, rfl⟩
  · cases c <;> simp only [bal_transfer_apply, bal_start, hd, Ne.symm hd, ↓reduceIte, eq_self_iff_true,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]
  · cases c <;> simp only [bal_transfer_apply, bal_start, hd, Ne.symm hd, ↓reduceIte, eq_self_iff_true,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false]

end AsyncSwapProtocol
