import AsyncSwapProtocol.V2.Settlement

/-!
# Non-negativity of wallet balances outside the PoolManager (v2)

`World.bal` is a signed ledger; this module proves that no wallet other than the PoolManager
is driven below zero by a v2 entry point.

Per ledger operation:
* `take` and `payOut` only move tokens out of the PoolManager, so they only credit wallets;
* `settle` debits the payer, so it needs `n ≤ bal c payer` at the point where it runs;
* every other operation leaves `bal` alone.

The guarded debits are the router's input settle in `swap` (`amountIn ≤ bal o.input owner`,
or `value ≤ bal o.input sender` for native input, `Model.lean:341`), the bid settle
(`priorityFee ≤ bal numeraire owner`, `Model.lean:343`) and the filler's settle in `fillOrder`
(`liveGross ≤ bal o.output sender`, `Model.lean:374`).

**Gap.** A buy order (`o.input = numeraire`) with a non-zero bid debits the owner's numeraire
twice, `amountIn` then `priorityFee`, but `swapGuard` checks each against the starting balance
on its own, never their sum.  The model lets that swap drive the owner negative, so
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
theorem BalNonNeg.transfer {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) (c : Currency) (s d : Address)
    (n : ℕ) (hn : s ≠ cfg.pm → (n : ℤ) ≤ t.w.bal c s) : BalNonNeg cfg (t.transfer c s d n).w := by
  intro c' x hx
  rw [bal_transfer_apply]
  have hx' := h c' x hx
  split_ifs <;> subst_vars <;> first | omega | (have := hn hx; omega)

theorem BalNonNeg.take {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b :
    BalNonNeg cfg (t.take cfg c d n b).w :=
  BalNonNeg.of_bal_eq (h.transfer c cfg.pm d n (fun h' => absurd rfl h')) rfl

theorem BalNonNeg.settle {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) (c : Currency) (p d : Address)
    (n : ℕ) (hn : p ≠ cfg.pm → (n : ℤ) ≤ t.w.bal c p) : BalNonNeg cfg (t.settle cfg c p d n).w :=
  BalNonNeg.of_bal_eq (h.transfer c p cfg.pm n hn) rfl

theorem BalNonNeg.mint {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b :
    BalNonNeg cfg (t.mint c d n b).w := h.of_bal_eq rfl
theorem BalNonNeg.burn {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b :
    BalNonNeg cfg (t.burn c d n b).w := h.of_bal_eq rfl
theorem BalNonNeg.poolSwap {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) ci co ai ao b :
    BalNonNeg cfg (t.poolSwap ci co ai ao b).w := h.of_bal_eq rfl
theorem BalNonNeg.setOrder {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) k i :
    BalNonNeg cfg (t.setOrder k i).w := h.of_bal_eq rfl
theorem BalNonNeg.deleteOrder {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) k :
    BalNonNeg cfg (t.deleteOrder k).w := h.of_bal_eq rfl
theorem BalNonNeg.setPendingNative {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) n :
    BalNonNeg cfg (t.setPendingNative n).w := h.of_bal_eq rfl

theorem BalNonNeg.payOut {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c d n b by_ :
    BalNonNeg cfg (t.payOut cfg c d n b by_).w := by
  unfold Tx.payOut; split_ifs
  · exact h.mint _ _ _ _
  · exact h.take _ _ _ _

/-! ## Hook bodies: they only credit wallets -/

theorem BalNonNeg.payOutBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) c r n :
    BalNonNeg cfg (Protocol.payOutBody cfg t c r n).w :=
  (h.burn _ _ _ _).payOut _ _ _ _ _

theorem BalNonNeg.settleBidBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) n :
    BalNonNeg cfg (Protocol.settleBidBody cfg t n).w := by
  unfold Protocol.settleBidBody; split_ifs
  · exact h.of_bal_eq rfl
  · exact h.of_bal_eq rfl

theorem BalNonNeg.reduceSideBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) k cp used received :
    BalNonNeg cfg (Protocol.reduceSideBody cfg t k cp used received).w := by
  have h2 := (h.payOutBody k.input cp used).settleBidBody
    ((OrderInfo.toSpec k (t.w.orders k)).donatedFee ⟨used, received⟩)
  simp only [Protocol.reduceSideBody]
  split_ifs
  · exact (h2.settleBidBody _).deleteOrder _
  · exact ((h2.settleBidBody _).payOutBody _ _ _).deleteOrder _
  · exact h2.setOrder _ _

theorem BalNonNeg.matchLoop {cfg : Config} : ∀ (ms : List MatchChoice) {t t' : Tx},
    BalNonNeg cfg t.w → Protocol.matchLoop cfg t ms = some t' → BalNonNeg cfg t'.w := by
  intro ms
  induction ms with
  | nil => intro t t' h e; simp only [Protocol.matchLoop, Option.some.injEq] at e; subst e; exact h
  | cons m ms ih =>
    intro t t' h e
    simp only [Protocol.matchLoop] at e
    split_ifs at e
    exact ih ((h.reduceSideBody _ _ _ _).reduceSideBody _ _ _ _) e

/-! ## Entry-point bodies -/

theorem bal_createBody (cfg : Config) (t : Tx) o p :
    (Protocol.createBody cfg t o p).w.bal = (t.transfer o.input p cfg.pm o.amountIn).w.bal := rfl

theorem BalNonNeg.createBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) o p
    (hn : p ≠ cfg.pm → (o.amountIn : ℤ) ≤ t.w.bal o.input p) : BalNonNeg cfg (Protocol.createBody cfg t o p).w :=
  (h.transfer _ _ _ _ hn).of_bal_eq (bal_createBody cfg t o p)

theorem BalNonNeg.priorityFeeBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) (o : Order)
    (hn : o.owner ≠ cfg.pm → (o.priorityFee : ℤ) ≤ t.w.bal numeraire o.owner) :
    BalNonNeg cfg (Protocol.priorityFeeBody cfg t o).w := by
  unfold Protocol.priorityFeeBody; split_ifs
  · exact h
  · exact ((h.settle _ _ _ _ hn).mint _ _ _ _).setOrder _ _

theorem BalNonNeg.liquidityFillBody {cfg : Config} {w : World} (h : BalNonNeg cfg w) o n :
    BalNonNeg cfg (Protocol.liquidityFillBody cfg w o n).w :=
  (((BalNonNeg.burn (t := Tx.start w) h _ _ _ _).poolSwap _ _ _ _ _).payOut _ _ _ _ _
    |>.settleBidBody _).deleteOrder _

theorem BalNonNeg.cancelBody {cfg : Config} {t : Tx} (h : BalNonNeg cfg t.w) o :
    BalNonNeg cfg (Protocol.cancelBody cfg t o).w :=
  ((h.payOutBody _ _ _).settleBidBody _).deleteOrder _

/-- `fillOrder`: the filler's payment is guarded by `fillGuard`; on the native leg the hook
    receives `value = live` and passes it straight on to the PoolManager. -/
theorem BalNonNeg.fillBody {cfg : Config} {w : World} {s o mp v} (h : BalNonNeg cfg w)
    (hg : fillGuard cfg w s o mp v) : BalNonNeg cfg (Protocol.fillBody cfg w s o v).w := by
  obtain ⟨hv, -⟩ := hg
  have hP := h o.output cfg.hook cfg.hook_ne_pm
  simp only [Protocol.fillBody]
  apply BalNonNeg.setPendingNative; apply BalNonNeg.deleteOrder; apply BalNonNeg.settleBidBody
  apply BalNonNeg.payOutBody; apply BalNonNeg.mint; apply BalNonNeg.payOut
  by_cases hn : cfg.isNative o.output = true
  · simp only [hn, ite_true] at hv ⊢
    obtain ⟨rfl, hle⟩ := hv
    refine BalNonNeg.settle (((BalNonNeg.transfer (t := Tx.start w) h _ _ _ _ (fun _ => hle)
      ).setPendingNative _).setPendingNative _) _ _ _ _ (fun _ => ?_)
    show _ ≤ ((Tx.start w).transfer o.output s cfg.hook (liveGross w o.key)).w.bal o.output cfg.hook
    rw [bal_transfer_apply]
    simp only [bal_start, ite_true]
    split_ifs <;> subst_vars <;> omega
  · simp only [hn, ite_false, Bool.false_eq_true] at hv ⊢
    exact BalNonNeg.settle (t := Tx.start w) h _ _ _ _ (fun _ => hv.2)

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
    have hgap' := hgap s o v up ms rfl
    have hown := (hswap s o v up ms rfl).2
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
      have h1 : BalNonNeg cfg (if cfg.isNative o.input = true
          then Protocol.createBody cfg ((Tx.start w).transfer o.input o.owner cfg.router v) o cfg.router
          else Protocol.createBody cfg (Tx.start w) o o.owner).w := by
        split_ifs with hn
        · simp only [hn, ite_true] at hin
          obtain ⟨rfl, hle⟩ := hin
          refine BalNonNeg.createBody (BalNonNeg.transfer (t := Tx.start w) hN _ _ _ _ (fun _ => hle))
            _ _ (fun _ => ?_)
          rw [bal_transfer_apply]
          have := hN o.input cfg.router cfg.router_ne_pm
          simp only [bal_start, ite_true]
          split_ifs <;> omega
        · simp only [hn, ite_false, Bool.false_eq_true] at hin
          exact BalNonNeg.createBody (t := Tx.start w) hN _ _ (fun _ => hin.2)
      refine h1.priorityFeeBody o (fun _ => ?_)
      by_cases hz : o.priorityFee = 0
      · rw [hz]; exact_mod_cast h1 numeraire o.owner hown
      · have hne : numeraire ≠ o.input := fun e => hz (hgap' e.symm)
        split_ifs <;> simp only [bal_createBody, bal_transfer_apply, bal_start, hne, ite_false] <;>
          exact hfee
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
