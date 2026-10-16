import AsyncSwapProtocol.V2.Invariants

/-!
# v2 protocol specification — part 4: conservation

For any finite set of addresses `S` that contains the PoolManager, the hook, the router and
every party of a transaction (the acting address, the makers of all open orders, the payout
recipient), the sum of each currency's ledger over `S` is unchanged by every entry point:
tokens only ever move between ledgers, never appear or vanish.  (Claims are not tokens; their
backing is `Backing`, and their meaning is `Escrow`.)
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

def total (c : Currency) (S : Finset Address) (w : World) : ℤ := ∑ a ∈ S, w.bal c a

theorem sum_adjust (f : Address → ℤ) (S : Finset Address) (x : Address) (g : ℤ → ℤ) (hx : x ∈ S) :
    ∑ a ∈ S, adjust f x g a = ∑ a ∈ S, f a - f x + g (f x) := by
  simp only [adjust]
  rw [← Finset.sum_erase_add _ _ hx, ← Finset.sum_erase_add S _ hx, Function.update_self]
  have : ∑ a ∈ S.erase x, Function.update f x (g (f x)) a = ∑ a ∈ S.erase x, f a :=
    Finset.sum_congr rfl (fun a ha => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)])
  rw [this]; ring

/-- A transfer between two members of `S` does not change the total over `S`. -/
theorem total_transfer (c c' : Currency) (S : Finset Address) (t : Tx) (src dst : Address) (n : ℕ)
    (hs : src ∈ S) (hd : dst ∈ S) : total c' S (t.transfer c src dst n).w = total c' S t.w := by
  simp only [total, Tx.transfer, Tx.debit, Tx.credit, Function.update_apply]
  split_ifs with hc
  · subst hc
    rw [sum_adjust _ _ _ _ hd, sum_adjust _ _ _ _ hs]
    simp only [adjust, Function.update_apply]
    split_ifs <;> omega
  · rfl

/-- Bodies preserving every total over `S`. -/
def TotalPreserved (S : Finset Address) (f : Tx → Tx) : Prop := ∀ t c, total c S (f t).w = total c S t.w

theorem totalPreserved_comp {S : Finset Address} {f g : Tx → Tx} (hf : TotalPreserved S f) (hg : TotalPreserved S g) :
    TotalPreserved S (fun t => g (f t)) := fun t c => by rw [hg, hf]

theorem total_mint (S) (t : Tx) c d n b c' : total c' S (t.mint c d n b).w = total c' S t.w := rfl
theorem total_burn (S) (t : Tx) c s n b c' : total c' S (t.burn c s n b).w = total c' S t.w := rfl
theorem total_donate (S) (t : Tx) c n b c' : total c' S (t.donate c n b).w = total c' S t.w := rfl
theorem total_poolSwap (S) (t : Tx) ci co ai ao b c' : total c' S (t.poolSwap ci co ai ao b).w = total c' S t.w := rfl
theorem total_addDelta (S) (t : Tx) c a d c' : total c' S (t.addDelta c a d).w = total c' S t.w := rfl
theorem total_accountSwap (S) (t : Tx) c s h n c' : total c' S (t.accountSwap c s h n).w = total c' S t.w := rfl
theorem total_setOrder (S) (t : Tx) k i c' : total c' S (t.setOrder k i).w = total c' S t.w := rfl
theorem total_createOrder (S) (t : Tx) k i c' : total c' S (t.createOrder k i).w = total c' S t.w := rfl
theorem total_deleteOrder (S) (t : Tx) k c' : total c' S (t.deleteOrder k).w = total c' S t.w := rfl
theorem total_setPendingNative (S) (t : Tx) n c' : total c' S (t.setPendingNative n).w = total c' S t.w := rfl
theorem total_useRouterCancelNonce (S) (t : Tx) m n c' : total c' S (t.useRouterCancelNonce m n).w = total c' S t.w := rfl
theorem total_start (S) (w : World) c' : total c' S (Tx.start w).w = total c' S w := rfl

theorem total_take (S) (cfg : Config) (t : Tx) c d n b c' (hpm : cfg.pm ∈ S) (hd : d ∈ S) :
    total c' S (t.take cfg c d n b).w = total c' S t.w := by
  simp only [Tx.take, total_addDelta]; exact total_transfer c c' S t _ _ n hpm hd

theorem total_settle (S) (cfg : Config) (t : Tx) c p d n c' (hpm : cfg.pm ∈ S) (hp : p ∈ S) :
    total c' S (t.settle cfg c p d n).w = total c' S t.w := by
  simp only [Tx.settle, total_addDelta]; exact total_transfer c c' S t _ _ n hp hpm

theorem total_payOut (S) (cfg : Config) (t : Tx) c d n b by_ c' (hpm : cfg.pm ∈ S) (hd : d ∈ S) :
    total c' S (t.payOut cfg c d n b by_).w = total c' S t.w := by
  unfold Tx.payOut; split_ifs
  · rfl
  · exact total_take S cfg t c d n by_ c' hpm hd

theorem total_payOutBody (S) (cfg : Config) (t : Tx) c r n c' (hpm : cfg.pm ∈ S) (hr : r ∈ S) :
    total c' S (payOutBody cfg t c r n).w = total c' S t.w := by
  simp only [payOutBody]; rw [total_payOut S cfg _ _ _ _ _ _ _ hpm hr]; rfl

theorem total_settleBidBody (S) (cfg : Config) (t : Tx) n c' :
    total c' S (settleBidBody cfg t n).w = total c' S t.w := by
  simp only [settleBidBody]; split_ifs <;> rfl

theorem total_createBody (S) (cfg : Config) (t : Tx) (o : Order) (payer : Address) c'
    (hpm : cfg.pm ∈ S) (hp : payer ∈ S) :
    total c' S (createBody cfg t o payer).w = total c' S t.w := by
  simp only [createBody]
  rw [total_settle S cfg _ _ _ _ _ _ hpm hp]; rfl

theorem total_priorityFeeBody (S) (cfg : Config) (t : Tx) (o : Order) c'
    (hpm : cfg.pm ∈ S) (ho : o.owner ∈ S) :
    total c' S (priorityFeeBody cfg t o).w = total c' S t.w := by
  simp only [priorityFeeBody]; split_ifs
  · rfl
  · simp only [total_setOrder, total_mint]; exact total_settle S cfg _ _ _ _ _ _ hpm ho

theorem total_reduceSideBody (S) (cfg : Config) (t : Tx) (k : OrderKey) (cp : Address) u r c'
    (hpm : cfg.pm ∈ S) (hcp : cp ∈ S) (hk : k.owner ∈ S) :
    total c' S (reduceSideBody cfg t k cp u r).w = total c' S t.w := by
  simp only [reduceSideBody]
  split_ifs <;>
    simp only [total_deleteOrder, total_setOrder, total_settleBidBody, total_payOutBody S cfg _ _ _ _ _ hpm hcp,
      total_payOutBody S cfg _ _ _ _ _ hpm hk]

/-- Every maker of an open order is in `S`. -/
def Makers (S : Finset Address) (w : World) : Prop := ∀ k ∈ w.openKeys, k.owner ∈ S

theorem makers_mono {S : Finset Address} {w w' : World} (h : Makers S w) (hs : w'.openKeys ⊆ w.openKeys) :
    Makers S w' := fun k hk => h k (hs hk)

theorem total_matchLoop (S) (cfg : Config) (hpm : cfg.pm ∈ S) : ∀ (ms : List MatchChoice) (t t' : Tx),
    Makers S t.w → matchLoop cfg t ms = some t' → ∀ c, total c S t'.w = total c S t.w := by
  intro ms
  induction ms with
  | nil => intro t t' _ h c; simp only [matchLoop, Option.some.injEq] at h; subst h; rfl
  | cons m ms ih =>
    intro t t' hM h c
    simp only [matchLoop] at h
    split_ifs at h with hg
    have hs := hM _ hg.1
    have hb := hM _ hg.2.1
    rw [ih _ _ (makers_mono hM (openKeys_matchPairBody_subset cfg _ _ _ _)) h c]
    simp only [matchPairBody, total_reduceSideBody S cfg _ _ _ _ _ _ hpm hs hb,
      total_reduceSideBody S cfg _ _ _ _ _ _ hpm hb hs]

/-- **Conservation.**  With `S` containing the PoolManager, hook and router, every open
    order's maker, and the action's own parties, no entry point changes any currency's total. -/
theorem step_conservation {cfg : Config} {w w' : World} {a : Action} {S : Finset Address}
    (hpm : cfg.pm ∈ S) (hhook : cfg.hook ∈ S) (hrouter : cfg.router ∈ S) (hM : Makers S w)
    (h : step cfg w a = some w')
    (hswap : ∀ s o v up ms, a = .swap s o v up ms → o.owner ∈ S ∧ s ∈ S)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ∈ S)
    (hredeem : ∀ s n r, a = .redeemNative s n r → r ∈ S) :
    ∀ c, total c S w' = total c S w := by
  intro c
  cases a with
  | swap s o v up ms =>
    obtain ⟨ho, hs⟩ := hswap s o v up ms rfl
    simp only [step, swap] at h
    split_ifs at h
    cases hbd : swapBody cfg w s o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      simp only [swapBody] at hbd
      have hM' : Makers S (priorityFeeBody cfg
          (if cfg.isNative o.input then createBody cfg ((Tx.start w).transfer o.input s cfg.router v) o cfg.router
           else createBody cfg (Tx.start w) o o.owner) o).w := by
        intro k hk
        rw [openKeys_priorityFeeBody] at hk
        split_ifs at hk <;> rw [openKeys_createBody, Finset.mem_insert] at hk <;>
          rcases hk with rfl | hk <;> first | exact ho | exact hM _ hk
      rw [total_matchLoop S cfg hpm ms _ t hM' hbd c, total_priorityFeeBody S cfg _ _ _ hpm ho]
      split_ifs
      · rw [total_createBody S cfg _ _ _ _ hpm hrouter, total_transfer _ _ _ _ _ _ _ hs hrouter]; rfl
      · rw [total_createBody S cfg _ _ _ _ hpm ho]; rfl
  | matchBook s mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hbd : matchLoop cfg (Tx.start w) ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
      exact total_matchLoop S cfg hpm ms _ t hM hbd c
  | fillOrder s o mp v =>
    have hs := hfill s o mp v rfl
    simp only [step, fillOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    have ho : o.owner ∈ S := hM _ hg.1.2.2.2.2.2
    simp only [fillBody]
    split_ifs
    all_goals
      simp only [total_setPendingNative, total_deleteOrder, total_settleBidBody,
        total_payOutBody S cfg _ _ _ _ _ hpm hs, total_mint, total_payOut S cfg _ _ _ _ _ _ _ hpm ho,
        total_settle S cfg _ _ _ _ _ _ hpm hhook, total_settle S cfg _ _ _ _ _ _ hpm hs,
        total_transfer _ _ _ _ _ _ _ hs hhook, total_start]
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    have ho : o.owner ∈ S := hM _ hg.2.1.2.2.2
    simp only [cancelBody, total_deleteOrder, total_settleBidBody, total_payOutBody S cfg _ _ _ _ _ hpm ho,
      total_start]
  | cancelWithSig s o nonce deadline now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    have ho : o.owner ∈ S := hM _ hg.1.2.2.2.2.2.2
    simp only [cancelBody, total_deleteOrder, total_settleBidBody, total_payOutBody S cfg _ _ _ _ _ hpm ho,
      total_useRouterCancelNonce, total_start]
  | fillFromPoolLiquidity s o amountOut =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h; subst h
    have ho : o.owner ∈ S := hM _ hg.1.1
    simp only [liquidityFillBody, total_deleteOrder, total_settleBidBody,
      total_payOut S cfg _ _ _ _ _ _ _ hpm ho, total_poolSwap, total_burn, total_start]
  | redeemNative s n r =>
    have hr := hredeem s n r rfl
    simp only [step, redeemNative] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h
    rw [total_take S cfg _ _ _ _ _ _ hpm hr]; rfl
  | updatePrice s o m =>
    simp only [step, updatePrice] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; rfl
  | setOrderingMode s mode =>
    simp only [step, setOrderingMode] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; rfl
  | setExecutor s e al =>
    simp only [step, Protocol.setExecutor, Option.some.injEq] at h; subst h; rfl

end AsyncSwapProtocol.V2
