import AsyncSwapProtocol.V2.Settlement

/-!
# Non-negativity of wallet balances outside the PoolManager (v2)

`World.bal` is a signed ledger; this module proves that no wallet other than the PoolManager
(whose balance is pinned by `Backing`) is driven below zero by any v2 entry point.

The argument, per ledger operation:
* `take` and `payOut` only move tokens *out of* the PoolManager, so they only credit wallets;
* `settle` debits the payer, so it needs `n ≤ bal c payer` at the point where it runs;
* every other operation leaves `bal` alone.

The guarded debits are the router's input settle in `swap` (`amountIn ≤ bal o.input owner`,
or `value ≤ bal o.input sender` for native input, `Model.lean:341`), the bid settle
(`priorityFee ≤ bal numeraire owner`, `Model.lean:343`) and the filler's settle in `fillOrder`
(`liveGross ≤ bal o.output sender`, `Model.lean:374`).

**Gap.** A *buy* order (`o.input = numeraire`) with a non-zero bid debits the owner's numeraire
twice — `amountIn`, then `priorityFee` — but `swapGuard` checks each against the starting
balance on its own, never their sum.  The model lets that swap drive the owner negative, so
`step_bal_nonneg` leaves exactly that case out (`hgap`).
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-- Every wallet balance outside the PoolManager is non-negative. -/
def BalNonNeg (cfg : Config) (w : World) : Prop := ∀ c a, a ≠ cfg.pm → 0 ≤ w.bal c a

theorem BalNonNeg.of_bal_eq {cfg : Config} {w w' : World} (h : BalNonNeg cfg w) (he : w'.bal = w.bal) :
    BalNonNeg cfg w' := fun c a ha => he ▸ h c a ha

/-! ## Ledger steps -/

/-- A transfer out of a wallet keeps it non-negative when the wallet held enough. -/
theorem BalNonNeg.transfer {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c s d n
    (hn : s ≠ cfg.pm → (n : ℤ) ≤ t.w.bal c s) : BalNonNeg cfg (t.transfer c s d n).w := by
  intro c' x hx
  rw [bal_transfer_apply]
  split_ifs with h1 h2 h3 h4
  · subst_vars; have := h c x hx; omega
  · subst_vars; have := h c x hx; omega
  · subst_vars; have := hn hx; omega
  · exact h _ _ hx
  · exact h _ _ hx

theorem BalNonNeg.take {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b :
    BalNonNeg cfg (t.take cfg c d n b).w :=
  BalNonNeg.of_bal_eq (h.transfer c cfg.pm d n (fun h' => absurd rfl h')) rfl

theorem BalNonNeg.settle {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c p d n
    (hn : p ≠ cfg.pm → (n : ℤ) ≤ t.w.bal c p) : BalNonNeg cfg (t.settle cfg c p d n).w :=
  BalNonNeg.of_bal_eq (h.transfer c p cfg.pm n hn) rfl

theorem BalNonNeg.payOut {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b by_ :
    BalNonNeg cfg (t.payOut cfg c d n b by_).w := by
  unfold Tx.payOut; split_ifs
  · exact h.of_bal_eq rfl
  · exact h.take _ _ _ _

/-! ## Hook bodies: they only credit wallets -/

theorem BalNonNeg.payOutBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c r n :
    BalNonNeg cfg (payOutBody cfg t c r n).w := by
  unfold payOutBody; exact BalNonNeg.payOut (t := t.burn _ _ _ _) h _ _ _ _ _

theorem bal_settleBidBody (cfg : Config) (t : Tx) n : (settleBidBody cfg t n).w.bal = t.w.bal := by
  unfold settleBidBody; split_ifs <;> rfl

theorem BalNonNeg.reduceSideBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) k cp used received :
    BalNonNeg cfg (reduceSideBody cfg t k cp used received).w := by
  have h1 := h.payOutBody k.input cp used
  have h2 := h1.of_bal_eq (bal_settleBidBody cfg _
    ((OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩))
  simp only [reduceSideBody]
  split_ifs
  · exact h2.of_bal_eq (bal_settleBidBody cfg _ _)
  · exact (((h2.of_bal_eq (bal_settleBidBody cfg _ _)).payOutBody _ _ _)).of_bal_eq rfl
  · exact h2.of_bal_eq rfl

theorem BalNonNeg.matchLoop {cfg : Config} : ∀ (ms : List MatchChoice) {t t' : Tx},
    BalNonNeg cfg t.w → Protocol.matchLoop cfg t ms = some t' → BalNonNeg cfg t'.w := by
  intro ms
  induction ms with
  | nil => intro t t' h e; simp only [Protocol.matchLoop, Option.some.injEq] at e; subst e; exact h
  | cons m ms ih =>
    intro t t' h e
    simp only [Protocol.matchLoop] at e
    split_ifs at e
    exact ih (by unfold matchPairBody; exact (h.reduceSideBody _ _ _ _).reduceSideBody _ _ _ _) e

/-! ## Entry-point bodies -/

theorem bal_createBody (cfg : Config) (t : Tx) o p :
    (createBody cfg t o p).w.bal = (t.transfer o.input p cfg.pm o.amountIn).w.bal := rfl

theorem bal_priorityFeeBody (cfg : Config) (t : Tx) (o : Order) (h : o.priorityFee ≠ 0) :
    (priorityFeeBody cfg t o).w.bal = (t.transfer numeraire o.owner cfg.pm o.priorityFee).w.bal := by
  unfold priorityFeeBody; rw [if_neg h]; rfl

theorem BalNonNeg.liquidityFillBody {cfg : Config} {w : World} (h : BalNonNeg cfg w) o n :
    BalNonNeg cfg (liquidityFillBody cfg w o n).w := by
  simp only [liquidityFillBody]
  exact ((BalNonNeg.payOut (t := ((Tx.start w).burn _ _ _ _).poolSwap _ _ _ _ _) h _ _ _ _ _).of_bal_eq
    (bal_settleBidBody cfg _ _)).of_bal_eq rfl

theorem BalNonNeg.cancelBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) o :
    BalNonNeg cfg (cancelBody cfg t o).w := by
  unfold cancelBody
  exact ((h.payOutBody _ _ _).of_bal_eq (bal_settleBidBody cfg _ _)).of_bal_eq rfl

/-- `fillOrder`: the filler's payment is guarded by `fillGuard`; the native leg passes through
    the hook (`value = live`), which pays it straight on to the PoolManager. -/
theorem BalNonNeg.fillBody {cfg : Config} {w : World} {s o mp v} (h : BalNonNeg cfg w)
    (hg : fillGuard cfg w s o mp v) : BalNonNeg cfg (fillBody cfg w s o v).w := by
  obtain ⟨hv, -⟩ := hg
  have h4 : BalNonNeg cfg (if cfg.isNative o.output then
      ((((Tx.start w).transfer o.output s cfg.hook v).setPendingNative v).setPendingNative
        ((((Tx.start w).transfer o.output s cfg.hook v).setPendingNative v).pendingNative
          - liveGross w o.key)).settle cfg o.output cfg.hook cfg.hook (liveGross w o.key)
      else (Tx.start w).settle cfg o.output s cfg.hook (liveGross w o.key)).w := by
    split_ifs with hn
    · rw [if_pos hn] at hv
      obtain ⟨rfl, hle⟩ := hv
      apply BalNonNeg.settle (t := ((Tx.start w).transfer o.output s cfg.hook (liveGross w o.key)).setPendingNative _)
      · exact (BalNonNeg.transfer (t := Tx.start w) h _ _ _ _ (fun _ => hle))
      · intro _
        show _ ≤ ((Tx.start w).transfer o.output s cfg.hook (liveGross w o.key)).w.bal o.output cfg.hook
        rw [bal_transfer_apply]
        have := h o.output cfg.hook cfg.hook_ne_pm
        have := h o.output s
        simp only [bal_start, if_true]
        split_ifs <;> subst_vars <;> omega
    · rw [if_neg hn] at hv
      exact BalNonNeg.settle (t := Tx.start w) h _ _ _ _ (fun _ => hv.2)
  have e : fillBody cfg w s o v = (((settleBidBody cfg (payOutBody cfg
      (((if cfg.isNative o.output then
      ((((Tx.start w).transfer o.output s cfg.hook v).setPendingNative v).setPendingNative
        ((((Tx.start w).transfer o.output s cfg.hook v).setPendingNative v).pendingNative
          - liveGross w o.key)).settle cfg o.output cfg.hook cfg.hook (liveGross w o.key)
      else (Tx.start w).settle cfg o.output s cfg.hook (liveGross w o.key)).payOut cfg o.output o.owner
        (w.orders o.key).amountOutMin (cfg.isNative o.output) cfg.hook).mint o.output cfg.vault
        (poolFee (w.orders o.key).amountOutMin) cfg.hook) o.input s (w.orders o.key).amountIn)
      (w.orders o.key).priorityFee).deleteOrder o.key).setPendingNative 0) := by
    simp only [fillBody]; split_ifs <;> rfl
  rw [e]
  exact (((((h4.payOut _ _ _ _ _).of_bal_eq rfl).payOutBody _ _ _).of_bal_eq
    (bal_settleBidBody cfg _ _)).of_bal_eq rfl).of_bal_eq rfl

/-! ## Entry points -/

/-- **Wallet balances outside the PoolManager stay non-negative across every v2 entry point**,
    except a buy-side `swap` with a non-zero bid (`hgap`; see the module docstring).
    Environment assumptions as in `step_escrow`. -/
theorem step_bal_nonneg {cfg : Config} {w w' : World} {a : Action}
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.hook ∧ o.owner ≠ cfg.pm)
    (_hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.hook)
    (_hredeem : ∀ s n r, a = .redeemNative s n r → s ≠ cfg.hook)
    (hgap : ∀ s o v up ms, a = .swap s o v up ms → o.input = numeraire → o.priorityFee = 0) :
    BalNonNeg cfg w → BalNonNeg cfg w' := by
  intro hN
  cases a with
  | swap s o v up ms =>
    obtain ⟨_, hop⟩ := hswap s o v up ms rfl
    have hgap := hgap s o v up ms rfl
    simp only [step, swap] at h
    split_ifs at h with hg
    obtain ⟨⟨hos, -, -, -, -, hin, hfee, -⟩, -⟩ := hg
    subst hos
    cases hbd : swapBody cfg w o.owner o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [swapBody] at hbd
      refine BalNonNeg.matchLoop ms ?_ hbd
      -- after the input settle: non-negative, and the owner's numeraire is untouched unless the
      -- input is the numeraire
      have h1 : BalNonNeg cfg (if cfg.isNative o.input = true
          then createBody cfg ((Tx.start w).transfer o.input o.owner cfg.router v) o cfg.router
          else createBody cfg (Tx.start w) o o.owner).w
          ∧ (o.input ≠ numeraire → (if cfg.isNative o.input = true
          then createBody cfg ((Tx.start w).transfer o.input o.owner cfg.router v) o cfg.router
          else createBody cfg (Tx.start w) o o.owner).w.bal numeraire o.owner = w.bal numeraire o.owner) := by
        split_ifs with hn
        · rw [if_pos hn] at hin
          obtain ⟨rfl, hle⟩ := hin
          have ht := BalNonNeg.transfer (t := Tx.start w) hN _ _ cfg.router _ (fun _ => hle)
          refine ⟨BalNonNeg.of_bal_eq (BalNonNeg.transfer ht _ _ cfg.pm _ (fun _ => ?_))
            (bal_createBody cfg _ o cfg.router), fun hne => ?_⟩
          · rw [bal_transfer_apply]
            have := hN o.input cfg.router cfg.router_ne_pm
            simp only [bal_start, if_true]
            split_ifs <;> subst_vars <;> omega
          · rw [bal_createBody, bal_transfer_apply, if_neg (Ne.symm hne), bal_transfer_apply,
              if_neg (Ne.symm hne)]; rfl
        · rw [if_neg hn] at hin
          refine ⟨BalNonNeg.of_bal_eq (BalNonNeg.transfer (t := Tx.start w) hN _ _ cfg.pm _
            (fun _ => hin.2)) (bal_createBody cfg _ o o.owner), fun hne => ?_⟩
          rw [bal_createBody, bal_transfer_apply, if_neg (Ne.symm hne)]; rfl
      obtain ⟨h1, h1e⟩ := h1
      by_cases hz : o.priorityFee = 0
      · unfold priorityFeeBody; rw [if_pos hz]; exact h1
      · refine BalNonNeg.of_bal_eq (BalNonNeg.transfer h1 _ _ cfg.pm _ (fun _ => ?_))
          (bal_priorityFeeBody cfg _ o hz)
        have hne : o.input ≠ numeraire := fun e => hz (hgap e)
        rw [h1e hne]; exact hfee
  | matchBook _ mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hl : Protocol.matchLoop cfg (Tx.start w) ms with
    | none => rw [hl] at h; exact absurd h (by simp)
    | some t =>
      rw [hl] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      exact BalNonNeg.matchLoop ms (t := Tx.start w) hN hl
  | fillOrder s o mp v =>
    simp only [step, fillOrder] at h
    split_ifs at h with hg; simp only [Option.some.injEq] at h; subst h
    exact hN.fillBody hg.1
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact BalNonNeg.cancelBody (t := Tx.start w) hN o
  | cancelWithSig _ o nonce dl now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact BalNonNeg.cancelBody (t := (Tx.start w).useRouterCancelNonce _ _) hN o
  | fillFromPoolLiquidity _ o n =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact hN.liquidityFillBody o n
  | redeemNative s n r =>
    simp only [step, redeemNative] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact BalNonNeg.take (t := (Tx.start w).burn _ _ _ _) hN _ _ _ _
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
