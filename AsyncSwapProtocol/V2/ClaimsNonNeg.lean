import AsyncSwapProtocol.V2.Invariants

/-!
# Non-negativity of every claim balance (v2)

The hook's own ERC-6909 claims are pinned by `Escrow` (hook claims = open input + escrowed
bids).  This module covers everyone else — makers, fillers, the vault, `NativeClaims`
redeemers: their claim balances never go negative across any v2 entry point.

The argument, per entry point:
* the only ledger operation that lowers a claim balance is `burn`;
* every `burn` inside a hook body (`payOutBody`, `settleBidBody`, the liquidity-fill input
  settle) burns the hook's own claim, so balances off the hook only grow (`Grows`);
* `redeemNative` burns the caller's claims, guarded by `amount ≤ claims false sender`
  (`NativeClaims.redeem` → `manager.burn`, which reverts on underflow);
* the hook's own balance at the end follows from `Escrow` after the step.

No entry point debits an off-hook claim without a guard, so there is no extra hypothesis.
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-- Every claim balance is non-negative. -/
def ClaimsNonNeg (_cfg : Config) (w : World) : Prop := ∀ c a, 0 ≤ w.claims c a

/-- Between two points of a transaction, no claim balance other than the hook's went down. -/
def Grows (cfg : Config) (t s : Tx) : Prop := ∀ c x, x ≠ cfg.hook → t.w.claims c x ≤ s.w.claims c x

theorem grows_refl (cfg : Config) (t : Tx) : Grows cfg t t := fun _ _ _ => le_refl _

theorem grows_trans {cfg : Config} {t s u : Tx} (h1 : Grows cfg t s) (h2 : Grows cfg s u) : Grows cfg t u :=
  fun c x hx => (h1 c x hx).trans (h2 c x hx)

theorem grows_of_claims {cfg : Config} {t s s' : Tx} (h : Grows cfg t s) (he : s'.w.claims = s.w.claims) :
    Grows cfg t s' := fun c x hx => he ▸ h c x hx

/-! ## Ledger steps, composed on the right -/

theorem grows_mint {cfg : Config} {t s : Tx} (h : Grows cfg t s) c d n b : Grows cfg t (s.mint c d n b) := by
  intro c' x hx
  have := h c' x hx
  rw [claims_mint_apply]
  split_ifs with h1 h2
  · subst h1 h2; omega
  · subst h1; exact this
  · exact this

theorem grows_burn_hook {cfg : Config} {t s : Tx} (h : Grows cfg t s) c n b :
    Grows cfg t (s.burn c cfg.hook n b) := by
  intro c' x hx
  have := h c' x hx
  rw [claims_burn_apply]
  split_ifs <;> subst_vars <;> exact this

theorem grows_transfer {cfg : Config} {t s : Tx} (h : Grows cfg t s) c a d n : Grows cfg t (s.transfer c a d n) :=
  grows_of_claims h rfl
theorem grows_take {cfg : Config} {t s : Tx} (h : Grows cfg t s) c d n b : Grows cfg t (s.take cfg c d n b) :=
  grows_of_claims h rfl
theorem grows_settle {cfg : Config} {t s : Tx} (h : Grows cfg t s) c p d n : Grows cfg t (s.settle cfg c p d n) :=
  grows_of_claims h rfl
theorem grows_addDelta {cfg : Config} {t s : Tx} (h : Grows cfg t s) c a d : Grows cfg t (s.addDelta c a d) :=
  grows_of_claims h rfl
theorem grows_accountSwap {cfg : Config} {t s : Tx} (h : Grows cfg t s) c a b n :
    Grows cfg t (s.accountSwap c a b n) := grows_of_claims h rfl
theorem grows_donate {cfg : Config} {t s : Tx} (h : Grows cfg t s) c n b : Grows cfg t (s.donate c n b) :=
  grows_of_claims h rfl
theorem grows_poolSwap {cfg : Config} {t s : Tx} (h : Grows cfg t s) ci co ai ao b :
    Grows cfg t (s.poolSwap ci co ai ao b) := grows_of_claims h rfl
theorem grows_setOrder {cfg : Config} {t s : Tx} (h : Grows cfg t s) k i : Grows cfg t (s.setOrder k i) :=
  grows_of_claims h rfl
theorem grows_createOrder {cfg : Config} {t s : Tx} (h : Grows cfg t s) k i : Grows cfg t (s.createOrder k i) :=
  grows_of_claims h rfl
theorem grows_deleteOrder {cfg : Config} {t s : Tx} (h : Grows cfg t s) k : Grows cfg t (s.deleteOrder k) :=
  grows_of_claims h rfl
theorem grows_setPendingNative {cfg : Config} {t s : Tx} (h : Grows cfg t s) n :
    Grows cfg t (s.setPendingNative n) := grows_of_claims h rfl
theorem grows_useRouterCancelNonce {cfg : Config} {t s : Tx} (h : Grows cfg t s) m n :
    Grows cfg t (s.useRouterCancelNonce m n) := grows_of_claims h rfl

theorem grows_payOut {cfg : Config} {t s : Tx} (h : Grows cfg t s) c d n b by_ :
    Grows cfg t (s.payOut cfg c d n b by_) := by
  unfold Tx.payOut; split_ifs
  · exact grows_mint h _ _ _ _
  · exact grows_take h _ _ _ _

theorem grows_ite {cfg : Config} {t a b : Tx} {p : Prop} [Decidable p] (ha : Grows cfg t a) (hb : Grows cfg t b) :
    Grows cfg t (if p then a else b) := by
  split_ifs
  · exact ha
  · exact hb

/-! ## Bodies -/

theorem grows_payOutBody {cfg : Config} {t s : Tx} (h : Grows cfg t s) c r n :
    Grows cfg t (payOutBody cfg s c r n) := by
  unfold payOutBody; exact grows_payOut (grows_burn_hook h _ _ _) _ _ _ _ _

theorem grows_settleBidBody {cfg : Config} {t s : Tx} (h : Grows cfg t s) n :
    Grows cfg t (settleBidBody cfg s n) := by
  unfold settleBidBody; split_ifs
  · exact grows_burn_hook (grows_donate h _ _ _) _ _ _
  · exact grows_mint (grows_burn_hook h _ _ _) _ _ _ _

theorem grows_reduceSideBody (cfg : Config) (t : Tx) k cp used received :
    Grows cfg t (reduceSideBody cfg t k cp used received) := by
  have h2 := grows_settleBidBody (grows_payOutBody (grows_refl cfg t) k.input cp used)
    ((OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩)
  simp only [reduceSideBody]
  split_ifs
  · exact grows_deleteOrder (grows_settleBidBody h2 _) _
  · exact grows_deleteOrder (grows_payOutBody (grows_settleBidBody h2 _) _ _ _) _
  · exact grows_setOrder h2 _ _

theorem grows_matchPairBody (cfg : Config) (t : Tx) s b r : Grows cfg t (matchPairBody cfg t s b r) := by
  unfold matchPairBody
  exact grows_trans (grows_reduceSideBody cfg t _ _ _ _) (grows_reduceSideBody cfg _ _ _ _ _)

theorem grows_matchLoop (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    matchLoop cfg t ms = some t' → Grows cfg t t' := by
  intro ms
  induction ms with
  | nil => intro t t' h; simp only [matchLoop, Option.some.injEq] at h; subst h; exact grows_refl cfg t
  | cons m ms ih =>
    intro t t' h
    simp only [matchLoop] at h
    split_ifs at h
    exact grows_trans (grows_matchPairBody cfg t _ _ _) (ih _ _ h)

theorem grows_createBody {cfg : Config} {t s : Tx} (h : Grows cfg t s) o p : Grows cfg t (createBody cfg s o p) := by
  simp only [createBody]
  exact grows_settle (grows_accountSwap (grows_createOrder (grows_mint h _ _ _ _) _ _) _ _ _ _) _ _ _ _

theorem grows_priorityFeeBody {cfg : Config} {t s : Tx} (h : Grows cfg t s) o :
    Grows cfg t (priorityFeeBody cfg s o) := by
  unfold priorityFeeBody; split_ifs
  · exact h
  · exact grows_setOrder (grows_mint (grows_settle h _ _ _ _) _ _ _ _) _ _

theorem grows_fillBody (cfg : Config) (w : World) s o v : Grows cfg (Tx.start w) (fillBody cfg w s o v) := by
  have g0 := grows_refl cfg (Tx.start w)
  have g1 := grows_ite (p := cfg.isNative o.output = true)
    (grows_setPendingNative (grows_transfer g0 o.output s cfg.hook v) v) g0
  have g2 := grows_ite (p := cfg.isNative o.output = true) g1
    (grows_settle g1 o.output s cfg.hook (liveGross w o.key))
  simp only [fillBody]
  exact grows_setPendingNative (grows_deleteOrder (grows_settleBidBody (grows_payOutBody
    (grows_mint (grows_payOut (grows_ite (grows_settle (grows_ite (grows_setPendingNative g2 _) g2) _ _ _ _)
      (grows_ite (grows_setPendingNative g2 _) g2)) _ _ _ _ _) _ _ _ _) _ _ _) _) _) _

theorem grows_cancelBody (cfg : Config) (t : Tx) o : Grows cfg t (cancelBody cfg t o) := by
  unfold cancelBody
  exact grows_deleteOrder (grows_settleBidBody (grows_payOutBody (grows_refl cfg t) _ _ _) _) _

theorem grows_liquidityFillBody (cfg : Config) (w : World) o n :
    Grows cfg (Tx.start w) (liquidityFillBody cfg w o n) := by
  simp only [liquidityFillBody]
  exact grows_deleteOrder (grows_settleBidBody (grows_payOut (grows_poolSwap
    (grows_burn_hook (grows_refl cfg _) _ _ _) _ _ _ _ _) _ _ _ _ _) _) _

/-! ## Entry points -/

/-- The hook's total obligation is a sum of natural-number order fields.  Re-proved here so
    this module does not depend on `NonNeg.lean`. -/
private theorem owed_nonneg' (c : Currency) (w : World) : 0 ≤ owed c w :=
  Finset.sum_nonneg (fun k _ => by unfold escrowOf; split_ifs <;> omega)

theorem ClaimsNonNeg.of_grows {cfg : Config} {w : World} {t : Tx} (hN : ClaimsNonNeg cfg w)
    (hE' : Escrow cfg t.w) (hg : Grows cfg (Tx.start w) t) : ClaimsNonNeg cfg t.w := by
  intro c x
  by_cases hx : x = cfg.hook
  · subst hx; rw [hE'.claims c]; exact owed_nonneg' c t.w
  · exact (hN c x).trans (hg c x hx)

/-- `NativeClaims.redeem` burns only the caller's claims, and only up to their balance. -/
theorem redeemNative_claims_nonneg {cfg : Config} {w w' : World} {s n r}
    (hN : ClaimsNonNeg cfg w) (h : redeemNative cfg w s n r = some w') : ClaimsNonNeg cfg w' := by
  simp only [redeemNative] at h
  split_ifs at h with hg
  simp only [Option.some.injEq] at h; subst h
  obtain ⟨_, _, hle, _⟩ := hg
  intro c x
  simp only [claims_take, claims_burn_apply, claims_start]
  split_ifs <;> subst_vars <;> first | (have := hN false x; omega) | exact hN _ _

/-- **Every claim balance stays non-negative across every v2 entry point.**  Environment
    assumptions as in `step_escrow` (which supplies the hook's own balance): makers, fillers
    and redeemers are users, never the hook or the PoolManager. -/
theorem step_claims_nonneg {cfg : Config} {w w' : World} {a : Action} (hE : Escrow cfg w)
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.hook ∧ o.owner ≠ cfg.pm)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.hook)
    (hredeem : ∀ s n r, a = .redeemNative s n r → s ≠ cfg.hook) :
    ClaimsNonNeg cfg w → ClaimsNonNeg cfg w' := by
  intro hN
  have hE' := step_escrow hE h hswap hfill hredeem
  cases a with
  | swap s o v up ms =>
    simp only [step, swap] at h
    split_ifs at h
    cases hbd : swapBody cfg w s o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [swapBody] at hbd
      refine hN.of_grows hE' (grows_trans ?_ (grows_matchLoop cfg ms _ _ hbd))
      apply grows_priorityFeeBody
      exact grows_ite (grows_createBody (grows_transfer (grows_refl cfg _) _ _ _ _) _ _)
        (grows_createBody (grows_refl cfg _) _ _)
  | matchBook _ mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hl : matchLoop cfg (Tx.start w) ms with
    | none => rw [hl] at h; exact absurd h (by simp)
    | some t =>
      rw [hl] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      exact hN.of_grows hE' (grows_matchLoop cfg ms _ _ hl)
  | fillOrder s o mp v =>
    simp only [step, fillOrder] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN.of_grows hE' (grows_fillBody cfg w s o v)
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN.of_grows hE' (grows_cancelBody cfg _ o)
  | cancelWithSig _ o nonce dl now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN.of_grows hE'
      (grows_trans (grows_useRouterCancelNonce (grows_refl cfg _) _ _) (grows_cancelBody cfg _ o))
  | fillFromPoolLiquidity _ o n =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN.of_grows hE' (grows_liquidityFillBody cfg w o n)
  | redeemNative s n r => exact redeemNative_claims_nonneg hN h
  | updatePrice s o m =>
    simp only [step, updatePrice] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN
  | setOrderingMode s m =>
    simp only [step, setOrderingMode] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN
  | setExecutor s e b =>
    simp only [step, Protocol.setExecutor, Option.some.injEq] at h; subst h
    exact hN

end AsyncSwapProtocol.V2
