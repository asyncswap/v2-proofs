import AsyncSwapProtocol.V2.Spec

/-!
# v2 protocol specification — part 2: settlement and the backing invariant

* `fill_settlement` / `cancel_settlement`: what each party ends up with, with native legs paid
  as PoolManager claims;
* `Backing`: the PoolManager's token balance equals the ERC-6909 supply plus the pool's own
  reserves, for every currency, and every entry point preserves it.  The proof goes through
  the potential `phi = bal pm − supply − reserves − Σ locker deltas`, which every PoolManager
  primitive leaves unchanged; at the start and end of an unlock all deltas are zero.

Environment assumption used here: the PoolManager is never itself a maker, filler or payout
recipient (`Users cfg w`).
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-! ## Evaluation lemmas -/

@[simp] theorem bal_start (w : World) : (Tx.start w).w.bal = w.bal := rfl
@[simp] theorem claims_start (w : World) : (Tx.start w).w.claims = w.claims := rfl
@[simp] theorem supply_start (w : World) : (Tx.start w).w.claimsSupply = w.claimsSupply := rfl
@[simp] theorem reserves_start (w : World) : (Tx.start w).w.reserves = w.reserves := rfl

@[simp] theorem bal_mint (t : Tx) c d n b : (t.mint c d n b).w.bal = t.w.bal := rfl
@[simp] theorem bal_burn (t : Tx) c s n b : (t.burn c s n b).w.bal = t.w.bal := rfl
@[simp] theorem bal_donate (t : Tx) c n b : (t.donate c n b).w.bal = t.w.bal := rfl
@[simp] theorem bal_poolSwap (t : Tx) ci co ai ao b : (t.poolSwap ci co ai ao b).w.bal = t.w.bal := rfl
@[simp] theorem bal_addDelta (t : Tx) c a d : (t.addDelta c a d).w.bal = t.w.bal := rfl
@[simp] theorem bal_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.bal = t.w.bal := rfl
@[simp] theorem bal_setOrder (t : Tx) k i : (t.setOrder k i).w.bal = t.w.bal := rfl
@[simp] theorem bal_createOrder (t : Tx) k i : (t.createOrder k i).w.bal = t.w.bal := rfl
@[simp] theorem bal_deleteOrder (t : Tx) k : (t.deleteOrder k).w.bal = t.w.bal := rfl
@[simp] theorem bal_setPendingNative (t : Tx) n : (t.setPendingNative n).w.bal = t.w.bal := rfl
@[simp] theorem bal_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.bal = t.w.bal := rfl

@[simp] theorem claims_transfer (t : Tx) c s d n : (t.transfer c s d n).w.claims = t.w.claims := rfl
@[simp] theorem claims_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.claims = t.w.claims := rfl
@[simp] theorem claims_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.claims = t.w.claims := rfl
@[simp] theorem claims_donate (t : Tx) c n b : (t.donate c n b).w.claims = t.w.claims := rfl
@[simp] theorem claims_poolSwap (t : Tx) ci co ai ao b : (t.poolSwap ci co ai ao b).w.claims = t.w.claims := rfl
@[simp] theorem claims_addDelta (t : Tx) c a d : (t.addDelta c a d).w.claims = t.w.claims := rfl
@[simp] theorem claims_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.claims = t.w.claims := rfl
@[simp] theorem claims_setOrder (t : Tx) k i : (t.setOrder k i).w.claims = t.w.claims := rfl
@[simp] theorem claims_createOrder (t : Tx) k i : (t.createOrder k i).w.claims = t.w.claims := rfl
@[simp] theorem claims_deleteOrder (t : Tx) k : (t.deleteOrder k).w.claims = t.w.claims := rfl
@[simp] theorem claims_setPendingNative (t : Tx) n : (t.setPendingNative n).w.claims = t.w.claims := rfl
@[simp] theorem claims_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.claims = t.w.claims := rfl

@[simp] theorem supply_transfer (t : Tx) c s d n : (t.transfer c s d n).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_donate (t : Tx) c n b : (t.donate c n b).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_poolSwap (t : Tx) ci co ai ao b : (t.poolSwap ci co ai ao b).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_addDelta (t : Tx) c a d : (t.addDelta c a d).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_setOrder (t : Tx) k i : (t.setOrder k i).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_createOrder (t : Tx) k i : (t.createOrder k i).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_deleteOrder (t : Tx) k : (t.deleteOrder k).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_setPendingNative (t : Tx) n : (t.setPendingNative n).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.claimsSupply = t.w.claimsSupply := rfl
@[simp] theorem supply_mint (t : Tx) c d n b :
    (t.mint c d n b).w.claimsSupply = Function.update t.w.claimsSupply c (t.w.claimsSupply c + n) := rfl
@[simp] theorem supply_burn (t : Tx) c s n b :
    (t.burn c s n b).w.claimsSupply = Function.update t.w.claimsSupply c (t.w.claimsSupply c - n) := rfl

@[simp] theorem reserves_transfer (t : Tx) c s d n : (t.transfer c s d n).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_mint (t : Tx) c d n b : (t.mint c d n b).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_burn (t : Tx) c s n b : (t.burn c s n b).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_addDelta (t : Tx) c a d : (t.addDelta c a d).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_setOrder (t : Tx) k i : (t.setOrder k i).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_createOrder (t : Tx) k i : (t.createOrder k i).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_deleteOrder (t : Tx) k : (t.deleteOrder k).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_setPendingNative (t : Tx) n : (t.setPendingNative n).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.reserves = t.w.reserves := rfl
@[simp] theorem reserves_donate (t : Tx) c n b :
    (t.donate c n b).w.reserves = Function.update t.w.reserves c (t.w.reserves c + n) := rfl
@[simp] theorem reserves_poolSwap (t : Tx) ci co ai ao b :
    (t.poolSwap ci co ai ao b).w.reserves =
      Function.update (Function.update t.w.reserves ci (t.w.reserves ci + ai)) co (t.w.reserves co - ao) := rfl

theorem bal_transfer_apply (t : Tx) (c : Currency) (s d : Address) (n : ℕ) (c' : Currency) (x : Address) :
    (t.transfer c s d n).w.bal c' x =
      if c' = c then
        (if x = d then (if d = s then t.w.bal c s - n else t.w.bal c d) + n
         else if x = s then t.w.bal c s - n else t.w.bal c x)
      else t.w.bal c' x := by
  simp only [Tx.transfer, Tx.debit, Tx.credit, adjust, Function.update_apply]
  split_ifs <;> simp_all

theorem claims_mint_apply (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (b : Address) (c' : Currency) (x : Address) :
    (t.mint c dst n b).w.claims c' x = if c' = c then (if x = dst then t.w.claims c dst + n else t.w.claims c x) else t.w.claims c' x := by
  simp only [Tx.mint, adjust, Function.update_apply]
  split_ifs <;> simp_all

theorem claims_burn_apply (t : Tx) (c : Currency) (src : Address) (n : ℕ) (b : Address) (c' : Currency) (x : Address) :
    (t.burn c src n b).w.claims c' x = if c' = c then (if x = src then t.w.claims c src - n else t.w.claims c x) else t.w.claims c' x := by
  simp only [Tx.burn, adjust, Function.update_apply]
  split_ifs <;> simp_all

/-! ## Backing: `bal pm = claimsSupply + reserves` -/

/-- Potential that every PoolManager primitive preserves. -/
def phi (cfg : Config) (t : Tx) (c : Currency) : ℤ :=
  t.w.bal c cfg.pm - t.w.claimsSupply c - t.w.reserves c
    - (t.delta c cfg.router + t.delta c cfg.hook + t.delta c cfg.vault + t.delta c cfg.nativeClaims)

def Locker (cfg : Config) (a : Address) : Prop :=
  a = cfg.router ∨ a = cfg.hook ∨ a = cfg.vault ∨ a = cfg.nativeClaims

def PhiPreserved (cfg : Config) (f : Tx → Tx) : Prop := ∀ t c, phi cfg (f t) c = phi cfg t c

theorem phiPreserved_comp {cfg : Config} {f g : Tx → Tx} (hf : PhiPreserved cfg f) (hg : PhiPreserved cfg g) :
    PhiPreserved cfg (fun t => g (f t)) := fun t c => by rw [hg, hf]

theorem sum_delta_addDelta (cfg : Config) (t : Tx) (c : Currency) (a : Address) (d : ℤ) (c' : Currency)
    (ha : Locker cfg a) :
    (t.addDelta c a d).delta c' cfg.router + (t.addDelta c a d).delta c' cfg.hook
      + (t.addDelta c a d).delta c' cfg.vault + (t.addDelta c a d).delta c' cfg.nativeClaims
    = t.delta c' cfg.router + t.delta c' cfg.hook + t.delta c' cfg.vault + t.delta c' cfg.nativeClaims
      + (if c' = c then d else 0) := by
  have h1 := cfg.router_ne_hook; have h2 := cfg.router_ne_vault; have h3 := cfg.hook_ne_vault
  have h4 := cfg.nc_ne_hook; have h5 := cfg.nc_ne_vault; have h6 := cfg.nc_ne_router
  simp only [delta_addDelta_apply]
  rcases ha with rfl | rfl | rfl | rfl <;> split_ifs <;> subst_vars <;> first | omega | simp_all

theorem phi_transfer (cfg : Config) (c : Currency) (s d : Address) (n : ℕ)
    (hs : s ≠ cfg.pm) (hd : d ≠ cfg.pm) : PhiPreserved cfg (fun t => t.transfer c s d n) := by
  intro t c'
  simp only [phi, bal_transfer_apply, supply_transfer, reserves_transfer, delta_transfer]
  split_ifs <;> simp_all

theorem phi_settle (cfg : Config) (c : Currency) (payer creditTo : Address) (n : ℕ)
    (hp : payer ≠ cfg.pm) (hc : Locker cfg creditTo) : PhiPreserved cfg (fun t => t.settle cfg c payer creditTo n) := by
  intro t c'
  simp only [phi, Tx.settle, bal_addDelta, bal_transfer_apply, supply_addDelta, supply_transfer,
    reserves_addDelta, reserves_transfer, sum_delta_addDelta cfg _ _ _ _ _ hc, delta_transfer]
  split_ifs <;> simp_all <;> omega

theorem phi_take (cfg : Config) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address)
    (hd : dst ≠ cfg.pm) (hb : Locker cfg by_) : PhiPreserved cfg (fun t => t.take cfg c dst n by_) := by
  intro t c'
  simp only [phi, Tx.take, bal_addDelta, bal_transfer_apply, supply_addDelta, supply_transfer,
    reserves_addDelta, reserves_transfer, sum_delta_addDelta cfg _ _ _ _ _ hb, delta_transfer]
  split_ifs <;> simp_all <;> omega

theorem phi_mint (cfg : Config) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address) (hb : Locker cfg by_) :
    PhiPreserved cfg (fun t => t.mint c dst n by_) := by
  intro t c'
  simp only [phi, bal_mint, supply_mint, reserves_mint, delta_mint, sum_delta_addDelta cfg _ _ _ _ _ hb,
    Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem phi_burn (cfg : Config) (c : Currency) (src : Address) (n : ℕ) (by_ : Address) (hb : Locker cfg by_) :
    PhiPreserved cfg (fun t => t.burn c src n by_) := by
  intro t c'
  simp only [phi, bal_burn, supply_burn, reserves_burn, delta_burn, sum_delta_addDelta cfg _ _ _ _ _ hb,
    Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem phi_donate (cfg : Config) (c : Currency) (n : ℕ) (by_ : Address) (hb : Locker cfg by_) :
    PhiPreserved cfg (fun t => t.donate c n by_) := by
  intro t c'
  simp only [phi, bal_donate, supply_donate, reserves_donate, delta_donate, sum_delta_addDelta cfg _ _ _ _ _ hb,
    Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem phi_poolSwap (cfg : Config) (ci co : Currency) (ai ao : ℕ) (by_ : Address) (hb : Locker cfg by_)
    (hne : ci ≠ co) : PhiPreserved cfg (fun t => t.poolSwap ci co ai ao by_) := by
  intro t c'
  simp only [phi, bal_poolSwap, supply_poolSwap, reserves_poolSwap, delta_poolSwap,
    sum_delta_addDelta cfg _ _ _ _ _ hb, Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem OrderKey.input_ne_output (k : OrderKey) : k.input ≠ k.output := by
  cases k.zeroForOne <;> simp [OrderKey.input, OrderKey.output]
theorem Order.input_ne_output (o : Order) : o.input ≠ o.output := OrderKey.input_ne_output o.key

theorem phi_accountSwap (cfg : Config) (c : Currency) (n : ℕ) :
    PhiPreserved cfg (fun t => t.accountSwap c cfg.router cfg.hook n) := by
  intro t c'
  simp only [phi, Tx.accountSwap, bal_addDelta, supply_addDelta, reserves_addDelta]
  rw [sum_delta_addDelta cfg _ _ _ _ _ (Or.inr (Or.inl rfl)), sum_delta_addDelta cfg _ _ _ _ _ (Or.inl rfl)]
  split_ifs <;> omega

theorem phi_payOut (cfg : Config) (c : Currency) (dst : Address) (n : ℕ) (asClaims : Bool) (by_ : Address)
    (hd : dst ≠ cfg.pm) (hb : Locker cfg by_) : PhiPreserved cfg (fun t => t.payOut cfg c dst n asClaims by_) := by
  intro t c'
  unfold Tx.payOut
  split_ifs
  · exact phi_mint cfg c dst n by_ hb t c'
  · exact phi_take cfg c dst n by_ hd hb t c'

theorem locker_hook (cfg : Config) : Locker cfg cfg.hook := Or.inr (Or.inl rfl)
theorem locker_router (cfg : Config) : Locker cfg cfg.router := Or.inl rfl
theorem locker_vault (cfg : Config) : Locker cfg cfg.vault := Or.inr (Or.inr (Or.inl rfl))
theorem locker_nc (cfg : Config) : Locker cfg cfg.nativeClaims := Or.inr (Or.inr (Or.inr rfl))

/-- Storage-only primitives do not touch `phi`. -/
theorem phi_setOrder (cfg : Config) k i : PhiPreserved cfg (fun t => t.setOrder k i) := fun _ _ => rfl
theorem phi_createOrder (cfg : Config) k i : PhiPreserved cfg (fun t => t.createOrder k i) := fun _ _ => rfl
theorem phi_deleteOrder (cfg : Config) k : PhiPreserved cfg (fun t => t.deleteOrder k) := fun _ _ => rfl
theorem phi_setPendingNative (cfg : Config) n : PhiPreserved cfg (fun t => t.setPendingNative n) := fun _ _ => rfl
theorem phi_useRouterCancelNonce (cfg : Config) m n : PhiPreserved cfg (fun t => t.useRouterCancelNonce m n) := fun _ _ => rfl

theorem phi_settleBidBody (cfg : Config) (n : ℕ) : PhiPreserved cfg (fun t => settleBidBody cfg t n) := by
  intro t c
  simp only [settleBidBody]
  split_ifs
  · rw [phi_burn cfg _ _ _ _ (locker_hook cfg), phi_donate cfg _ _ _ (locker_hook cfg)]
  · rw [phi_mint cfg _ _ _ _ (locker_hook cfg), phi_burn cfg _ _ _ _ (locker_hook cfg)]

theorem phi_payOutBody (cfg : Config) (c : Currency) (r : Address) (n : ℕ) (hr : r ≠ cfg.pm) :
    PhiPreserved cfg (fun t => payOutBody cfg t c r n) := by
  intro t c'
  simp only [payOutBody]
  rw [phi_payOut cfg _ _ _ _ _ hr (locker_hook cfg), phi_burn cfg _ _ _ _ (locker_hook cfg)]

theorem phi_createBody (cfg : Config) (o : Order) (payer : Address) (hp : payer ≠ cfg.pm) :
    PhiPreserved cfg (fun t => createBody cfg t o payer) := by
  intro t c
  simp only [createBody]
  rw [phi_settle cfg _ _ _ _ hp (locker_router cfg), phi_accountSwap, phi_createOrder,
    phi_mint cfg _ _ _ _ (locker_hook cfg)]

theorem phi_priorityFeeBody (cfg : Config) (o : Order) (ho : o.owner ≠ cfg.pm) :
    PhiPreserved cfg (fun t => priorityFeeBody cfg t o) := by
  intro t c
  simp only [priorityFeeBody]
  split_ifs
  · rfl
  · rw [phi_setOrder, phi_mint cfg _ _ _ _ (locker_hook cfg), phi_settle cfg _ _ _ _ ho (locker_hook cfg)]

theorem phi_reduceSideBody (cfg : Config) (k : OrderKey) (cp : Address) (u r : ℕ)
    (hcp : cp ≠ cfg.pm) (hk : k.owner ≠ cfg.pm) :
    PhiPreserved cfg (fun t => reduceSideBody cfg t k cp u r) := by
  intro t c
  simp only [reduceSideBody]
  split_ifs
  all_goals
    simp only [phi_deleteOrder cfg _ _ c, phi_setOrder cfg _ _ _ c, phi_settleBidBody cfg _ _ c,
      phi_payOutBody cfg _ _ _ hcp _ c, phi_payOutBody cfg _ _ _ hk _ c]

/-- No open order is owned by the PoolManager (environment assumption: the PoolManager never
    acts as a maker). -/
def Users (cfg : Config) (w : World) : Prop := ∀ k ∈ w.openKeys, k.owner ≠ cfg.pm

@[simp] theorem openKeys_settleBidBody (cfg : Config) (t : Tx) (n : ℕ) :
    (settleBidBody cfg t n).w.openKeys = t.w.openKeys := by
  simp only [settleBidBody]; split_ifs <;> rfl
@[simp] theorem openKeys_payOutBody (cfg : Config) (t : Tx) c r n :
    (payOutBody cfg t c r n).w.openKeys = t.w.openKeys := by
  simp only [payOutBody, Tx.payOut]; split_ifs <;> rfl
@[simp] theorem openKeys_createBody (cfg : Config) (t : Tx) (o : Order) (p : Address) :
    (createBody cfg t o p).w.openKeys = insert o.key t.w.openKeys := rfl
@[simp] theorem openKeys_priorityFeeBody (cfg : Config) (t : Tx) (o : Order) :
    (priorityFeeBody cfg t o).w.openKeys = t.w.openKeys := by
  simp only [priorityFeeBody]; split_ifs <;> rfl

theorem openKeys_reduceSideBody_subset (cfg : Config) (t : Tx) (k : OrderKey) cp u r :
    (reduceSideBody cfg t k cp u r).w.openKeys ⊆ t.w.openKeys := by
  simp only [reduceSideBody]
  split_ifs <;> simp [Tx.deleteOrder, Tx.setOrder, Finset.erase_subset]

theorem openKeys_matchPairBody_subset (cfg : Config) (t : Tx) sk bk rb :
    (matchPairBody cfg t sk bk rb).w.openKeys ⊆ t.w.openKeys :=
  (openKeys_reduceSideBody_subset cfg _ _ _ _ _).trans (openKeys_reduceSideBody_subset cfg _ _ _ _ _)

theorem users_mono {cfg : Config} {w w' : World} (hu : Users cfg w) (hs : w'.openKeys ⊆ w.openKeys) :
    Users cfg w' := fun k hk => hu k (hs hk)

theorem matchLoop_phi (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    Users cfg t.w → matchLoop cfg t ms = some t' → ∀ c, phi cfg t' c = phi cfg t c := by
  intro ms
  induction ms with
  | nil => intro t t' _ h c; simp only [matchLoop, Option.some.injEq] at h; subst h; rfl
  | cons m ms ih =>
    intro t t' hu h c
    simp only [matchLoop] at h
    split_ifs at h with hg
    have hs : m.sellKey.owner ≠ cfg.pm := hu _ hg.1
    have hb : m.buyKey.owner ≠ cfg.pm := hu _ hg.2.1
    have hu' : Users cfg (matchPairBody cfg t m.sellKey m.buyKey m.restingBuy).w :=
      users_mono hu (openKeys_matchPairBody_subset cfg _ _ _ _)
    rw [ih _ _ hu' h c]
    simp only [matchPairBody, phi_reduceSideBody cfg _ _ _ _ hs hb _ c, phi_reduceSideBody cfg _ _ _ _ hb hs _ c]

/-- `bal c pm = claimsSupply c + reserves c`. -/
def Backing (cfg : Config) (w : World) : Prop := ∀ c, w.bal c cfg.pm = w.claimsSupply c + w.reserves c

theorem backing_iff_phi (cfg : Config) (w : World) : Backing cfg w ↔ ∀ c, phi cfg (Tx.start w) c = 0 := by
  simp only [Backing, phi, Tx.start, add_zero]
  constructor <;> intro h c <;> have := h c <;> omega

theorem phi_zero_of_deltasZero {cfg : Config} {t : Tx} (hz : t.deltasZero cfg) (c : Currency) :
    phi cfg t c = t.w.bal c cfg.pm - t.w.claimsSupply c - t.w.reserves c := by
  obtain ⟨h1, h2, h3, h4⟩ := hz c; simp [phi, h1, h2, h3, h4]

/-- **Backing is preserved by every v2 entry point**, given that the acting addresses are users. -/
theorem step_backing {cfg : Config} {w w' : World} {a : Action} (hb : Backing cfg w) (hu : Users cfg w)
    (h : step cfg w a = some w')
    (hsender : ∀ s o v up ms, a = .swap s o v up ms → o.owner ≠ cfg.pm ∧ s ≠ cfg.pm)
    (hfill : ∀ s o mp v, a = .fillOrder s o mp v → s ≠ cfg.pm)
    (hredeem : ∀ s n r, a = .redeemNative s n r → r ≠ cfg.pm) :
    Backing cfg w' := by
  rw [backing_iff_phi] at hb ⊢
  intro c
  have key : ∀ (t : Tx), t.w = w' → t.deltasZero cfg → phi cfg t c = 0 →
      phi cfg (Tx.start w') c = 0 := by
    intro t ht hz hp
    rw [phi_zero_of_deltasZero hz] at hp
    simp [phi, Tx.start, ← ht, hp]
  cases a with
  | swap s o v up ms =>
    obtain ⟨ho, hs⟩ := hsender s o v up ms rfl
    simp only [step, swap] at h
    split_ifs at h
    cases hbd : swapBody cfg w s o v ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h with hz; simp only [Option.some.injEq] at h
      apply key t h hz
      simp only [swapBody] at hbd
      have hu' : Users cfg (priorityFeeBody cfg
          (if cfg.isNative o.input then createBody cfg ((Tx.start w).transfer o.input s cfg.router v) o cfg.router
           else createBody cfg (Tx.start w) o o.owner) o).w := by
        intro k hk
        rw [openKeys_priorityFeeBody] at hk
        split_ifs at hk <;> rw [openKeys_createBody, Finset.mem_insert] at hk <;>
          rcases hk with rfl | hk <;> first | exact ho | exact hu _ hk
      rw [matchLoop_phi cfg ms _ t hu' hbd c]
      split_ifs
      · simp only [phi_priorityFeeBody cfg o ho _ c, phi_createBody cfg o _ cfg.router_ne_pm _ c,
          phi_transfer cfg _ _ _ _ hs cfg.router_ne_pm _ c]
        exact hb c
      · simp only [phi_priorityFeeBody cfg o ho _ c, phi_createBody cfg o _ ho _ c]
        exact hb c
  | matchBook s mm ms =>
    simp only [step, matchBook] at h
    split_ifs at h
    cases hbd : matchLoop cfg (Tx.start w) ms with
    | none => rw [hbd] at h; exact absurd h (by simp)
    | some t =>
      rw [hbd] at h; simp only at h; split_ifs at h with hz; simp only [Option.some.injEq] at h
      apply key t h hz
      rw [matchLoop_phi cfg ms _ t hu hbd c]; exact hb c
  | fillOrder s o mp v =>
    have hs := hfill s o mp v rfl
    simp only [step, fillOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    have ho : o.owner ≠ cfg.pm := hu _ hg.1.2.2.2.2.2
    apply key _ h hg.2
    simp only [fillBody]
    split_ifs
    all_goals
      simp only [phi_setPendingNative cfg _ _ c, phi_deleteOrder cfg _ _ c, phi_settleBidBody cfg _ _ c,
        phi_payOutBody cfg _ _ _ hs _ c, phi_mint cfg _ _ _ _ (locker_hook cfg) _ c,
        phi_payOut cfg _ _ _ _ _ ho (locker_hook cfg) _ c,
        phi_settle cfg _ _ _ _ cfg.hook_ne_pm (locker_hook cfg) _ c,
        phi_settle cfg _ _ _ _ hs (locker_hook cfg) _ c,
        phi_transfer cfg _ _ _ _ hs cfg.hook_ne_pm _ c]
      exact hb c
  | cancelOrder s o =>
    simp only [step, cancelOrder] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    have ho : o.owner ≠ cfg.pm := hu _ hg.2.1.2.2.2
    apply key _ h hg.2.2
    simp only [cancelBody, phi_deleteOrder cfg _ _ c, phi_settleBidBody cfg _ _ c,
      phi_payOutBody cfg _ _ _ ho _ c]
    exact hb c
  | cancelWithSig s o nonce deadline now =>
    simp only [step, cancelWithSig] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    have ho : o.owner ≠ cfg.pm := hu _ hg.1.2.2.2.2.2.2
    apply key _ h hg.2
    simp only [cancelBody, phi_deleteOrder cfg _ _ c, phi_settleBidBody cfg _ _ c,
      phi_payOutBody cfg _ _ _ ho _ c, phi_useRouterCancelNonce cfg _ _ _ c]
    exact hb c
  | fillFromPoolLiquidity s o amountOut =>
    simp only [step, fillFromPoolLiquidity] at h
    split_ifs at h with hg
    simp only [Option.some.injEq] at h
    have ho : o.owner ≠ cfg.pm := hu _ hg.1.1
    apply key _ h hg.2
    simp only [liquidityFillBody, phi_deleteOrder cfg _ _ c, phi_settleBidBody cfg _ _ c,
      phi_payOut cfg _ _ _ _ _ ho (locker_hook cfg) _ c,
      phi_poolSwap cfg _ _ _ _ _ (locker_hook cfg) (Order.input_ne_output o) _ c,
      phi_burn cfg _ _ _ _ (locker_hook cfg) _ c]
    exact hb c
  | redeemNative s n r =>
    have hr := hredeem s n r rfl
    simp only [step, redeemNative] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    have hz : (((Tx.start w).burn false s n cfg.nativeClaims).take cfg false r n cfg.nativeClaims).deltasZero cfg := by
      intro c'
      have h1 := cfg.nc_ne_router; have h2 := cfg.nc_ne_hook; have h3 := cfg.nc_ne_vault
      simp only [Tx.take, delta_transfer, delta_burn, delta_addDelta_apply, delta_start]
      split_ifs <;> subst_vars <;> first | omega | simp_all
    apply key _ h hz
    rw [phi_take cfg _ _ _ _ hr (locker_nc cfg), phi_burn cfg _ _ _ _ (locker_nc cfg)]; exact hb c
  | updatePrice s o m =>
    simp only [step, updatePrice] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; simpa [phi, Tx.start, Tx.setOrder] using hb c
  | setOrderingMode s mode =>
    simp only [step, setOrderingMode] at h
    split_ifs at h; simp only [Option.some.injEq] at h; subst h; simpa [phi, Tx.start] using hb c
  | setExecutor s e al =>
    simp only [step, Protocol.setExecutor, Option.some.injEq] at h; subst h
    simpa [phi, Tx.start, Tx.setExecutor] using hb c

end AsyncSwapProtocol.V2
