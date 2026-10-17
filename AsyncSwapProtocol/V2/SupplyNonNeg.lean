import AsyncSwapProtocol.V2.ClaimsNonNeg

/-!
# Non-negativity of pool reserves and of the ERC-6909 claim supply (v2)

These are the two PoolManager-side totals that are still open after `ClaimsNonNeg`.

* **Claim supply.** No existing invariant ties the ghost `claimsSupply` to the claim balances
  (there is no `Backing` structure in the model), so `SupplyEq` states it first:
  `claimsSupply c = Σ a ∈ S, claims c a` for a finite set `S` of holders outside which every
  claim balance is zero (addresses are `ℕ`, so the sum needs a finite support).  `mint` and
  `burn` move one balance and the supply by the same amount, and nothing else touches either,
  so `SupplyEq` is preserved by every entry point with no hypothesis.  With `ClaimsNonNeg`,
  `Finset.sum_nonneg` gives `0 ≤ claimsSupply c`.
* **Reserves.** `reserves` grows under `donate` and only falls in `poolSwap`, which runs only
  inside `fillFromPoolLiquidity`.  That entry point's guard already carries
  `amountOut ≤ reserves o.output` (`liquidityFillGuard`), and the input and output currencies
  differ, so reserves stay non-negative with no added hypothesis.
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-- Every pool reserve is non-negative. -/
def ReservesNonNeg (w : World) : Prop := ∀ c, 0 ≤ w.reserves c

/-- The ghost ERC-6909 total supply is the sum of the claim balances, over a finite support. -/
def SupplyEq (w : World) : Prop :=
  ∀ c, ∃ S : Finset Address, (∀ a ∉ S, w.claims c a = 0) ∧ w.claimsSupply c = ∑ a ∈ S, w.claims c a

/-- **Under `SupplyEq` and `ClaimsNonNeg`, the claim supply is non-negative.** -/
theorem claimsSupply_nonneg {cfg : Config} {w : World} (hS : SupplyEq w) (hN : ClaimsNonNeg cfg w)
    (c : Currency) : 0 ≤ w.claimsSupply c := by
  obtain ⟨S, _, h⟩ := hS c
  rw [h]; exact Finset.sum_nonneg (fun a _ => hN c a)

/-- Moving one claim balance and the supply by the same `k` preserves `SupplyEq`. -/
theorem SupplyEq.bump {w w' : World} (h : SupplyEq w) (c : Currency) (d : Address) (k : ℤ)
    (hc : w'.claims = Function.update w.claims c (Function.update (w.claims c) d (w.claims c d + k)))
    (hs : w'.claimsSupply = Function.update w.claimsSupply c (w.claimsSupply c + k)) : SupplyEq w' := by
  intro c'
  obtain ⟨S, hz, hsum⟩ := h c'
  by_cases hc' : c' = c
  · subst hc'
    have hins : ∑ a ∈ insert d S, w.claims c' a = ∑ a ∈ S, w.claims c' a := by
      by_cases hd : d ∈ S
      · rw [Finset.insert_eq_of_mem hd]
      · rw [Finset.sum_insert hd, hz d hd, zero_add]
    refine ⟨insert d S, fun a ha => ?_, ?_⟩
    · rw [Finset.mem_insert, not_or] at ha
      rw [hc, Function.update_self, Function.update_of_ne ha.1]; exact hz a ha.2
    · rw [hs, hc, Function.update_self, Function.update_self,
        Finset.sum_update_of_mem (Finset.mem_insert_self d S), ← hins,
        Finset.sum_eq_add_sum_diff_singleton (Finset.mem_insert_self d S), hsum, ← hins,
        Finset.sum_eq_add_sum_diff_singleton (Finset.mem_insert_self d S)]
      ring
  · refine ⟨S, fun a ha => ?_, ?_⟩
    · rw [hc, Function.update_of_ne hc']; exact hz a ha
    · rw [hs, hc, Function.update_of_ne hc', Function.update_of_ne hc']; exact hsum

/-! ## Between two points of a transaction: reserves only grow, `SupplyEq` carries over -/

/-- No reserve went down from `t` to `s`, and `SupplyEq` carries from `t` to `s`. -/
def Tracks (t s : Tx) : Prop := (∀ c, t.w.reserves c ≤ s.w.reserves c) ∧ (SupplyEq t.w → SupplyEq s.w)

theorem tracks_refl (t : Tx) : Tracks t t := ⟨fun _ => le_refl _, id⟩

theorem tracks_trans {t s u : Tx} (h1 : Tracks t s) (h2 : Tracks s u) : Tracks t u :=
  ⟨fun c => (h1.1 c).trans (h2.1 c), h2.2 ∘ h1.2⟩

/-- A step that leaves reserves, claims and supply alone. -/
theorem tracks_of_eq {t s s' : Tx} (h : Tracks t s) (hr : s'.w.reserves = s.w.reserves)
    (hc : s'.w.claims = s.w.claims) (hs : s'.w.claimsSupply = s.w.claimsSupply) : Tracks t s' := by
  refine ⟨fun c => hr ▸ h.1 c, fun hS c => ?_⟩
  obtain ⟨S, hz, hsum⟩ := h.2 hS c
  exact ⟨S, hc ▸ hz, hc ▸ hs ▸ hsum⟩

theorem tracks_mint {t s : Tx} (h : Tracks t s) c d n b : Tracks t (s.mint c d n b) :=
  ⟨h.1, fun hS => (h.2 hS).bump c d n rfl rfl⟩

theorem tracks_burn {t s : Tx} (h : Tracks t s) c d n b : Tracks t (s.burn c d n b) :=
  ⟨h.1, fun hS => (h.2 hS).bump c d (-(n : ℤ)) (by simp only [burn, adjust, sub_eq_add_neg])
    (by simp only [burn, sub_eq_add_neg])⟩

theorem tracks_donate {t s : Tx} (h : Tracks t s) c n b : Tracks t (s.donate c n b) := by
  refine ⟨fun c' => (h.1 c').trans ?_, fun hS => h.2 hS⟩
  simp only [donate, Function.update_apply]; split_ifs <;> omega

theorem tracks_transfer {t s : Tx} (h : Tracks t s) c a d n : Tracks t (s.transfer c a d n) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_take {cfg : Config} {t s : Tx} (h : Tracks t s) c d n b : Tracks t (s.take cfg c d n b) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_settle {cfg : Config} {t s : Tx} (h : Tracks t s) c p d n : Tracks t (s.settle cfg c p d n) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_accountSwap {t s : Tx} (h : Tracks t s) c a b n : Tracks t (s.accountSwap c a b n) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_setOrder {t s : Tx} (h : Tracks t s) k i : Tracks t (s.setOrder k i) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_createOrder {t s : Tx} (h : Tracks t s) k i : Tracks t (s.createOrder k i) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_deleteOrder {t s : Tx} (h : Tracks t s) k : Tracks t (s.deleteOrder k) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_setPendingNative {t s : Tx} (h : Tracks t s) n : Tracks t (s.setPendingNative n) :=
  tracks_of_eq h rfl rfl rfl
theorem tracks_useRouterCancelNonce {t s : Tx} (h : Tracks t s) m n : Tracks t (s.useRouterCancelNonce m n) :=
  tracks_of_eq h rfl rfl rfl

theorem tracks_payOut {cfg : Config} {t s : Tx} (h : Tracks t s) c d n b by_ :
    Tracks t (s.payOut cfg c d n b by_) := by
  unfold Tx.payOut; split_ifs
  · exact tracks_mint h _ _ _ _
  · exact tracks_take h _ _ _ _

theorem tracks_ite {t a b : Tx} {p : Prop} [Decidable p] (ha : Tracks t a) (hb : Tracks t b) :
    Tracks t (if p then a else b) := by
  split_ifs
  · exact ha
  · exact hb

/-! ## Bodies (every body except the pool fill's `poolSwap`) -/

theorem tracks_payOutBody {cfg : Config} {t s : Tx} (h : Tracks t s) c r n :
    Tracks t (payOutBody cfg s c r n) := by
  unfold payOutBody; exact tracks_payOut (tracks_burn h _ _ _ _) _ _ _ _ _

theorem tracks_settleBidBody {cfg : Config} {t s : Tx} (h : Tracks t s) n :
    Tracks t (settleBidBody cfg s n) := by
  unfold settleBidBody; split_ifs
  · exact tracks_burn (tracks_donate h _ _ _) _ _ _ _
  · exact tracks_mint (tracks_burn h _ _ _ _) _ _ _ _

theorem tracks_reduceSideBody (cfg : Config) (t : Tx) k cp used received :
    Tracks t (reduceSideBody cfg t k cp used received) := by
  have h2 := tracks_settleBidBody (cfg := cfg) (tracks_payOutBody (tracks_refl t) k.input cp used)
    ((OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩)
  simp only [reduceSideBody]
  split_ifs
  · exact tracks_deleteOrder (tracks_settleBidBody h2 _) _
  · exact tracks_deleteOrder (tracks_payOutBody (tracks_settleBidBody h2 _) _ _ _) _
  · exact tracks_setOrder h2 _ _

theorem tracks_matchPairBody (cfg : Config) (t : Tx) s b r : Tracks t (matchPairBody cfg t s b r) := by
  unfold matchPairBody
  exact tracks_trans (tracks_reduceSideBody cfg t _ _ _ _) (tracks_reduceSideBody cfg _ _ _ _ _)

theorem tracks_matchLoop (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    matchLoop cfg t ms = some t' → Tracks t t' := by
  intro ms
  induction ms with
  | nil => intro t t' h; simp only [matchLoop, Option.some.injEq] at h; subst h; exact tracks_refl t
  | cons m ms ih =>
    intro t t' h
    simp only [matchLoop] at h
    split_ifs at h
    exact tracks_trans (tracks_matchPairBody cfg t _ _ _) (ih _ _ h)

theorem tracks_createBody {cfg : Config} {t s : Tx} (h : Tracks t s) o p : Tracks t (createBody cfg s o p) := by
  simp only [createBody]
  exact tracks_settle (tracks_accountSwap (tracks_createOrder (tracks_mint h _ _ _ _) _ _) _ _ _ _) _ _ _ _

theorem tracks_priorityFeeBody {cfg : Config} {t s : Tx} (h : Tracks t s) o :
    Tracks t (priorityFeeBody cfg s o) := by
  unfold priorityFeeBody; split_ifs
  · exact h
  · exact tracks_setOrder (tracks_mint (tracks_settle h _ _ _ _) _ _ _ _) _ _

theorem tracks_fillBody (cfg : Config) (w : World) s o v : Tracks (Tx.start w) (fillBody cfg w s o v) := by
  have g0 := tracks_refl (Tx.start w)
  have g1 := tracks_ite (p := cfg.isNative o.output = true)
    (tracks_setPendingNative (tracks_transfer g0 o.output s cfg.hook v) v) g0
  have g2 := tracks_ite (p := cfg.isNative o.output = true) g1
    (tracks_settle (cfg := cfg) g1 o.output s cfg.hook (liveGross w o.key))
  simp only [fillBody]
  exact tracks_setPendingNative (tracks_deleteOrder (tracks_settleBidBody (tracks_payOutBody
    (tracks_mint (tracks_payOut (tracks_ite (tracks_settle (tracks_ite (tracks_setPendingNative g2 _) g2) _ _ _ _)
      (tracks_ite (tracks_setPendingNative g2 _) g2)) _ _ _ _ _) _ _ _ _) _ _ _) _) _) _

theorem tracks_cancelBody (cfg : Config) (t : Tx) o : Tracks t (cancelBody cfg t o) := by
  unfold cancelBody
  exact tracks_deleteOrder (tracks_settleBidBody (tracks_payOutBody (tracks_refl t) _ _ _) _) _

/-- The pool fill: `poolSwap` lowers the output reserve by `amountOut`, which the guard bounds
    by `reserves o.output`; the input reserve only grows; everything after only grows. -/
theorem liquidityFill_inv {cfg : Config} {w : World} {o : Order} {n : ℕ}
    (hg : (n : ℤ) ≤ w.reserves o.output) :
    (ReservesNonNeg w → ReservesNonNeg (liquidityFillBody cfg w o n).w)
    ∧ (SupplyEq w → SupplyEq (liquidityFillBody cfg w o n).w) := by
  set t1 := (Tx.start w).burn o.input cfg.hook (w.orders o.key).amountIn cfg.hook
  set t2 := t1.poolSwap o.input o.output (w.orders o.key).amountIn n cfg.hook
  have h1 : Tracks (Tx.start w) t1 := tracks_burn (tracks_refl _) _ _ _ _
  have h2 : SupplyEq w → SupplyEq t2.w := h1.2
  have hr : ReservesNonNeg w → ReservesNonNeg t2.w := by
    intro hR c
    have hne : o.input ≠ o.output := by
      simp only [Order.input, Order.output, OrderKey.input, OrderKey.output]; cases o.key.zeroForOne <;> decide
    simp only [t2, t1, poolSwap, burn, Tx.start, Function.update_apply]
    split_ifs with ho hi
    · subst ho; omega
    · subst hi; have := hR o.input; omega
    · exact hR c
  have h3 : Tracks t2 (liquidityFillBody cfg w o n) := by
    simp only [liquidityFillBody]
    exact tracks_deleteOrder (tracks_settleBidBody (tracks_payOut (tracks_refl t2) _ _ _ _ _) _) _
  exact ⟨fun hR c => (hr hR c).trans (h3.1 c), h3.2 ∘ h2⟩

/-! ## Entry points -/

theorem Tracks.inv {w : World} {t : Tx} (h : Tracks (Tx.start w) t) :
    (ReservesNonNeg w → ReservesNonNeg t.w) ∧ (SupplyEq w → SupplyEq t.w) :=
  ⟨fun hR c => (hR c).trans (h.1 c), h.2⟩

/-- Both invariants at once, across every v2 entry point, with no hypothesis. -/
theorem step_supply_inv {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w') :
    (ReservesNonNeg w → ReservesNonNeg w') ∧ (SupplyEq w → SupplyEq w') := by
  cases a with
  | swap s o v up ms =>
    simp only [step, swap] at h
    split_ifs at h
    cases hbd : swapBody cfg w s o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [swapBody] at hbd
      refine Tracks.inv (tracks_trans ?_ (tracks_matchLoop cfg ms _ _ hbd))
      apply tracks_priorityFeeBody
      exact tracks_ite (tracks_createBody (tracks_transfer (tracks_refl _) _ _ _ _) _ _)
        (tracks_createBody (tracks_refl _) _ _)
  | matchBook _ mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hl : matchLoop cfg (Tx.start w) ms with
    | none => rw [hl] at h; exact absurd h (by simp)
    | some t =>
      rw [hl] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      exact Tracks.inv (tracks_matchLoop cfg ms _ _ hl)
  | fillOrder s o mp v =>
    simp only [step, fillOrder] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact Tracks.inv (tracks_fillBody cfg w s o v)
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact Tracks.inv (tracks_cancelBody cfg _ o)
  | cancelWithSig _ o nonce dl now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact Tracks.inv
      (tracks_trans (tracks_useRouterCancelNonce (tracks_refl _) _ _) (tracks_cancelBody cfg _ o))
  | fillFromPoolLiquidity _ o n =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h with hg; simp only [Option.some.injEq] at h; subst h
    exact liquidityFill_inv hg.1.2.2.2.1
  | redeemNative s n r =>
    simp only [step, redeemNative] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact Tracks.inv (tracks_take (tracks_burn (tracks_refl _) _ _ _ _) _ _ _ _)
  | updatePrice s o m =>
    simp only [step, updatePrice] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact Tracks.inv (tracks_setOrder (tracks_refl _) _ _)
  | setOrderingMode s m =>
    simp only [step, setOrderingMode] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact ⟨id, id⟩
  | setExecutor s e b =>
    simp only [step, Protocol.setExecutor, Option.some.injEq] at h; subst h
    exact ⟨id, id⟩

/-- **Pool reserves stay non-negative across every v2 entry point.**  No added hypothesis: the
    only debit is `poolSwap` in `fillFromPoolLiquidity`, bounded by its guard. -/
theorem step_reserves_nonneg {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w') :
    ReservesNonNeg w → ReservesNonNeg w' :=
  (step_supply_inv h).1

/-- **`claimsSupply = Σ claims` is preserved by every v2 entry point.** -/
theorem step_supplyEq {cfg : Config} {w w' : World} {a : Action} (h : step cfg w a = some w') :
    SupplyEq w → SupplyEq w' :=
  (step_supply_inv h).2

/-- **The ERC-6909 claim supply stays non-negative across every v2 entry point**, under the
    environment assumptions of `step_claims_nonneg`. -/
theorem step_claimsSupply_nonneg {cfg : Config} {w w' : World} {a : Action} (hE : Escrow cfg w)
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.hook ∧ o.owner ≠ cfg.pm)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.hook)
    (hredeem : ∀ s n r, a = .redeemNative s n r → s ≠ cfg.hook)
    (hS : SupplyEq w) (hN : ClaimsNonNeg cfg w) (c : Currency) : 0 ≤ w'.claimsSupply c :=
  claimsSupply_nonneg (step_supplyEq h hS) (step_claims_nonneg hE h hswap hfill hredeem hN) c

end AsyncSwapProtocol.V2
