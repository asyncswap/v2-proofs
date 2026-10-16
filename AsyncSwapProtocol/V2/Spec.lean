import AsyncSwapProtocol.V2.Model

/-!
# v2 protocol specification — part 1

* every body is PoolManager-delta neutral (so every unlock branch, including up to eight
  matches, leaves router / hook / vault / NativeClaims deltas at zero);
* frame: fill, cancel and liquidity fill touch only their order; a create or `matchBook`
  touches only the incoming order and the chosen counterparties;
* bridge: `_reduceAfterMatch` as modelled here stores exactly `AsyncSwap.Order.reduce` or
  deletes the order, so `AsyncSwapSpec/Reduce.lean` (`maker_limit_honored`, …) applies to the
  state machine's partial fills;
* bids: after the create unlock every stored bid is escrowed; fill / cancel / match settle it
  completely (donated or forfeited) and never refund it.
-/

namespace AsyncSwapProtocol.V2
open Protocol Tx

/-! ## Evaluation lemmas -/

@[simp] theorem delta_transfer (t : Tx) c s d n : (t.transfer c s d n).delta = t.delta := rfl
@[simp] theorem delta_setOrder (t : Tx) k i : (t.setOrder k i).delta = t.delta := rfl
@[simp] theorem delta_createOrder (t : Tx) k i : (t.createOrder k i).delta = t.delta := rfl
@[simp] theorem delta_deleteOrder (t : Tx) k : (t.deleteOrder k).delta = t.delta := rfl
@[simp] theorem delta_setExecutor (t : Tx) m e a : (t.setExecutor m e a).delta = t.delta := rfl
@[simp] theorem delta_useHookNonce (t : Tx) m n : (t.useHookNonce m n).delta = t.delta := rfl
@[simp] theorem delta_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).delta = t.delta := rfl
@[simp] theorem delta_usePermit2Nonce (t : Tx) m n : (t.usePermit2Nonce m n).delta = t.delta := rfl
@[simp] theorem delta_setPendingNative (t : Tx) n : (t.setPendingNative n).delta = t.delta := rfl
@[simp] theorem delta_start (w : World) : (Tx.start w).delta = fun _ _ => 0 := rfl
@[simp] theorem delta_mint (t : Tx) c d n b : (t.mint c d n b).delta = (t.addDelta c b (-(n : ℤ))).delta := rfl
@[simp] theorem delta_burn (t : Tx) c s n b : (t.burn c s n b).delta = (t.addDelta c b (n : ℤ)).delta := rfl
@[simp] theorem delta_donate (t : Tx) c n b : (t.donate c n b).delta = (t.addDelta c b (-(n : ℤ))).delta := rfl
@[simp] theorem delta_poolSwap (t : Tx) ci co ai ao b :
    (t.poolSwap ci co ai ao b).delta = ((t.addDelta ci b (-(ai : ℤ))).addDelta co b (ao : ℤ)).delta := rfl

theorem delta_addDelta_apply (t : Tx) (c : Currency) (a : Address) (d : ℤ) (c' : Currency) (x : Address) :
    (t.addDelta c a d).delta c' x =
      if c' = c then (if x = a then t.delta c a + d else t.delta c x) else t.delta c' x := by
  simp only [Tx.addDelta, adjust, Function.update_apply]
  split_ifs <;> simp_all

@[simp] theorem orders_transfer (t : Tx) c s d n : (t.transfer c s d n).w.orders = t.w.orders := rfl
@[simp] theorem orders_mint (t : Tx) c d n b : (t.mint c d n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_burn (t : Tx) c s n b : (t.burn c s n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_donate (t : Tx) c n b : (t.donate c n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_poolSwap (t : Tx) ci co ai ao b : (t.poolSwap ci co ai ao b).w.orders = t.w.orders := rfl
@[simp] theorem orders_take cfg (t : Tx) c d n b : (t.take cfg c d n b).w.orders = t.w.orders := rfl
@[simp] theorem orders_settle cfg (t : Tx) c p d n : (t.settle cfg c p d n).w.orders = t.w.orders := rfl
@[simp] theorem orders_accountSwap (t : Tx) c s h n : (t.accountSwap c s h n).w.orders = t.w.orders := rfl
@[simp] theorem orders_addDelta (t : Tx) c a d : (t.addDelta c a d).w.orders = t.w.orders := rfl
@[simp] theorem orders_payOut cfg (t : Tx) c d n b by_ : (t.payOut cfg c d n b by_).w.orders = t.w.orders := by
  unfold Tx.payOut; split_ifs <;> rfl
@[simp] theorem orders_setPendingNative (t : Tx) n : (t.setPendingNative n).w.orders = t.w.orders := rfl
@[simp] theorem orders_start (w : World) : (Tx.start w).w.orders = w.orders := rfl
@[simp] theorem orders_setOrder (t : Tx) k i : (t.setOrder k i).w.orders = Function.update t.w.orders k i := rfl
@[simp] theorem orders_createOrder (t : Tx) k i : (t.createOrder k i).w.orders = Function.update t.w.orders k i := rfl
@[simp] theorem orders_deleteOrder (t : Tx) k :
    (t.deleteOrder k).w.orders = Function.update t.w.orders k ⟨0, 0, 0, false⟩ := rfl
@[simp] theorem orders_useRouterCancelNonce (t : Tx) m n : (t.useRouterCancelNonce m n).w.orders = t.w.orders := rfl

theorem orders_settleBidBody (cfg : Config) (t : Tx) (n : ℕ) : (settleBidBody cfg t n).w.orders = t.w.orders := by
  unfold settleBidBody; split_ifs <;> rfl
theorem orders_payOutBody (cfg : Config) (t : Tx) c r n : (payOutBody cfg t c r n).w.orders = t.w.orders := by
  simp [payOutBody]

/-! ## Delta neutrality -/

/-- A body is *delta-neutral* if it leaves every locker delta where it found it. -/
def DeltaNeutral (f : Tx → Tx) : Prop := ∀ t c a, (f t).delta c a = t.delta c a

theorem deltaNeutral_comp {f g : Tx → Tx} (hf : DeltaNeutral f) (hg : DeltaNeutral g) :
    DeltaNeutral (fun t => g (f t)) := fun t c a => by rw [hg, hf]

theorem settleBidBody_neutral (cfg : Config) (n : ℕ) : DeltaNeutral (fun t => settleBidBody cfg t n) := by
  intro t c a
  simp only [settleBidBody]
  split_ifs <;> simp only [delta_burn, delta_mint, delta_donate, delta_addDelta_apply] <;>
    split_ifs <;> subst_vars <;> omega

theorem payOut_neutral_after_burn (cfg : Config) (c : Currency) (r : Address) (n : ℕ) (b : Bool) :
    DeltaNeutral (fun t => (t.burn c cfg.hook n cfg.hook).payOut cfg c r n b cfg.hook) := by
  intro t c' a
  simp only [Tx.payOut, Tx.take]
  split_ifs <;> simp only [delta_mint, delta_burn, delta_transfer, delta_addDelta_apply] <;>
    split_ifs <;> subst_vars <;> omega

theorem payOutBody_neutral (cfg : Config) (c : Currency) (r : Address) (n : ℕ) :
    DeltaNeutral (fun t => payOutBody cfg t c r n) :=
  payOut_neutral_after_burn cfg c r n _

theorem createBody_neutral (cfg : Config) (o : Order) (payer : Address) :
    DeltaNeutral (fun t => createBody cfg t o payer) := by
  intro t c a
  have hrh := cfg.router_ne_hook
  simp only [createBody, Tx.settle, Tx.accountSwap, delta_transfer, delta_createOrder, delta_mint,
    delta_addDelta_apply]
  split_ifs <;> subst_vars <;> first | omega | simp_all

theorem priorityFeeBody_neutral (cfg : Config) (o : Order) :
    DeltaNeutral (fun t => priorityFeeBody cfg t o) := by
  intro t c a
  simp only [priorityFeeBody]
  split_ifs
  · rfl
  · simp only [delta_setOrder, Tx.settle, delta_mint, delta_transfer, delta_addDelta_apply]
    split_ifs <;> subst_vars <;> omega

theorem reduceSideBody_neutral (cfg : Config) (k : OrderKey) (cp : Address) (used received : ℕ) :
    DeltaNeutral (fun t => reduceSideBody cfg t k cp used received) := by
  intro t c a
  simp only [reduceSideBody]
  split_ifs <;>
    simp only [delta_deleteOrder, delta_setOrder, payOutBody_neutral cfg _ _ _ _ c a,
      settleBidBody_neutral cfg _ _ c a]

theorem matchPairBody_neutral (cfg : Config) (sk bk : OrderKey) (rb : Bool) :
    DeltaNeutral (fun t => matchPairBody cfg t sk bk rb) := by
  intro t c a
  simp only [matchPairBody, reduceSideBody_neutral cfg _ _ _ _ _ c a]

theorem matchLoop_neutral (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    matchLoop cfg t ms = some t' → ∀ c a, t'.delta c a = t.delta c a := by
  intro ms
  induction ms with
  | nil => intro t t' h c a; simp only [matchLoop, Option.some.injEq] at h; subst h; rfl
  | cons m ms ih =>
    intro t t' h c a
    simp only [matchLoop] at h
    split_ifs at h
    rw [ih _ _ h, matchPairBody_neutral]

theorem start_deltasZero (cfg : Config) (w : World) : (Tx.start w).deltasZero cfg := by
  intro c; simp

theorem deltasZero_of_neutral {cfg : Config} {f : Tx → Tx} (hf : DeltaNeutral f) {t : Tx}
    (ht : t.deltasZero cfg) : (f t).deltasZero cfg := by
  intro c; obtain ⟨h1, h2, h3, h4⟩ := ht c
  exact ⟨by rw [hf, h1], by rw [hf, h2], by rw [hf, h3], by rw [hf, h4]⟩

/-- **The create unlock is delta-neutral however many matches it performs.** -/
theorem swapBody_deltasZero {cfg : Config} {w : World} {sender : Address} {o : Order} {value : ℕ}
    {ms : List MatchChoice} {t : Tx} (h : swapBody cfg w sender o value ms = some t) : t.deltasZero cfg := by
  simp only [swapBody] at h
  intro c
  have hz := matchLoop_neutral cfg ms _ t h
  have hz' : ∀ a, t.delta c a = 0 := fun a => by
    rw [hz]
    split_ifs <;> simp [priorityFeeBody_neutral cfg o _ c a, createBody_neutral cfg o _ _ c a]
  exact ⟨hz' _, hz' _, hz' _, hz' _⟩

theorem matchBookBody_deltasZero {cfg : Config} {w : World} {ms : List MatchChoice} {t : Tx}
    (h : matchLoop cfg (Tx.start w) ms = some t) : t.deltasZero cfg := by
  intro c
  have hz := matchLoop_neutral cfg ms _ t h
  exact ⟨by rw [hz]; rfl, by rw [hz]; rfl, by rw [hz]; rfl, by rw [hz]; rfl⟩

theorem cancelBody_deltasZero (cfg : Config) (t : Tx) (o : Order) (ht : t.deltasZero cfg) :
    (cancelBody cfg t o).deltasZero cfg := by
  simp only [cancelBody]
  have := deltasZero_of_neutral (cfg := cfg)
    (deltaNeutral_comp (payOutBody_neutral cfg o.input o.owner (t.w.orders o.key).amountIn)
      (settleBidBody_neutral cfg (t.w.orders o.key).priorityFee)) ht
  intro c; obtain ⟨h1, h2, h3, h4⟩ := this c
  exact ⟨h1, h2, h3, h4⟩

theorem liquidityFillBody_deltasZero (cfg : Config) (w : World) (o : Order) (amountOut : ℕ) :
    (liquidityFillBody cfg w o amountOut).deltasZero cfg := by
  intro c
  have hrh := cfg.router_ne_hook
  have hhv := cfg.hook_ne_vault
  have hnh := cfg.nc_ne_hook
  simp only [liquidityFillBody, delta_deleteOrder, settleBidBody_neutral cfg _ _ c, Tx.payOut]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (split_ifs <;> simp only [delta_mint, Tx.take, delta_transfer, delta_poolSwap, delta_burn,
       delta_addDelta_apply, delta_start] <;> split_ifs <;> subst_vars <;> omega)

theorem fillBody_deltasZero (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) :
    (fillBody cfg w sender o value).deltasZero cfg := by
  intro c
  have hrh := cfg.router_ne_hook
  have hhv := cfg.hook_ne_vault
  have hnh := cfg.nc_ne_hook
  have hlive : (liveGross w o.key : ℤ) = (w.orders o.key).amountOutMin + poolFee (w.orders o.key).amountOutMin := by
    simp [liveGross, gross]
  simp only [fillBody, delta_setPendingNative, delta_deleteOrder, settleBidBody_neutral cfg _ _ c,
    payOutBody_neutral cfg _ _ _ _ c, Tx.payOut]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (split_ifs <;> simp only [delta_mint, Tx.take, Tx.settle, delta_transfer, delta_setPendingNative,
       delta_addDelta_apply, delta_start] <;> split_ifs <;> subst_vars <;> omega)

/-- **Completeness**: the PoolManager's end-of-unlock check never rejects a transaction whose
    contract-level checks passed (every entry point). -/
theorem fillOrder_eq_some_iff (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) :
    (∃ w', fillOrder cfg w sender o maxPrice value = some w') ↔ fillGuard cfg w sender o maxPrice value := by
  simp [fillOrder, fillBody_deltasZero]

theorem swap_eq_some_iff (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ)
    (up : UserParams) (ms : List MatchChoice) :
    (∃ w', swap cfg w sender o value up ms = some w') ↔
      swapGuard cfg w sender o value up ∧ ms.length ≤ maxMatchesPerCall
        ∧ ∃ t, swapBody cfg w sender o value ms = some t := by
  unfold swap
  split_ifs with hg
  · cases h : swapBody cfg w sender o value ms with
    | none => simp
    | some t =>
      constructor
      · intro _; exact ⟨hg.1, hg.2, t, rfl⟩
      · intro _
        refine ⟨t.w, ?_⟩
        show (if t.deltasZero cfg then some t.w else none) = some t.w
        rw [if_pos (swapBody_deltasZero h)]
  · constructor
    · rintro ⟨w', hw⟩; simp at hw
    · rintro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ hg

/-! ## Frame: which orders an action can touch -/

theorem orders_reduceSideBody_ne (cfg : Config) (t : Tx) (k k' : OrderKey) cp u r (hk : k' ≠ k) :
    (reduceSideBody cfg t k cp u r).w.orders k' = t.w.orders k' := by
  simp only [reduceSideBody]
  split_ifs <;> simp [orders_settleBidBody, orders_payOutBody, Function.update_of_ne hk]

/-- Keys a list of matches may touch. -/
def touched : List MatchChoice → Finset OrderKey
  | [] => ∅
  | m :: ms => insert m.sellKey (insert m.buyKey (touched ms))

theorem matchLoop_frame (cfg : Config) : ∀ (ms : List MatchChoice) (t t' : Tx),
    matchLoop cfg t ms = some t' → ∀ k, k ∉ touched ms → t'.w.orders k = t.w.orders k := by
  intro ms
  induction ms with
  | nil => intro t t' h k _; simp only [matchLoop, Option.some.injEq] at h; subst h; rfl
  | cons m ms ih =>
    intro t t' h k hk
    simp only [touched, Finset.mem_insert, not_or] at hk
    simp only [matchLoop] at h
    split_ifs at h
    rw [ih _ _ h k hk.2.2]
    simp only [matchPairBody]
    rw [orders_reduceSideBody_ne _ _ _ _ _ _ _ hk.2.1, orders_reduceSideBody_ne _ _ _ _ _ _ _ hk.1]

theorem orders_createBody (cfg : Config) (t : Tx) (o : Order) (payer : Address) :
    (createBody cfg t o payer).w.orders
      = Function.update t.w.orders o.key ⟨o.amountIn, o.amountOutMin, o.priorityFee, decide (o.priorityFee = 0)⟩ := by
  simp [createBody]

/-- **After the create unlock, before matching, the new order is stored with its bid escrowed.** -/
theorem created_order_escrowed (cfg : Config) (t : Tx) (o : Order) (payer : Address) :
    (priorityFeeBody cfg (createBody cfg t o payer) o).w.orders o.key
      = ⟨o.amountIn, o.amountOutMin, o.priorityFee, true⟩ := by
  simp only [priorityFeeBody]
  split_ifs with h
  · simp [orders_createBody, h]
  · simp [orders_createBody]

/-- **Frame for `swap`**: only the incoming order and the chosen counterparties change. -/
theorem swap_frame {cfg : Config} {w w' : World} {sender : Address} {o : Order} {value : ℕ} {up : UserParams}
    {ms : List MatchChoice} (h : swap cfg w sender o value up ms = some w')
    {k : OrderKey} (hk : k ≠ o.key) (hm : k ∉ touched ms) : w'.orders k = w.orders k := by
  unfold swap at h
  split_ifs at h
  cases hb : swapBody cfg w sender o value ms with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some t =>
    rw [hb] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
    simp only [swapBody] at hb
    rw [matchLoop_frame cfg ms _ t hb k hm]
    simp only [priorityFeeBody]
    split_ifs <;> simp [orders_createBody, Function.update_of_ne hk]

theorem matchBook_frame {cfg : Config} {w w' : World} {maxMatches : ℕ} {ms : List MatchChoice}
    (h : matchBook cfg w maxMatches ms = some w') {k : OrderKey} (hm : k ∉ touched ms) :
    w'.orders k = w.orders k := by
  unfold matchBook at h
  split_ifs at h
  cases hb : matchLoop cfg (Tx.start w) ms with
  | none => rw [hb] at h; exact absurd h (by simp)
  | some t =>
    rw [hb] at h; simp only at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
    exact matchLoop_frame cfg ms _ t hb k hm

/-- Fill, cancel and liquidity fill delete exactly their order and touch no other. -/
theorem fill_orders {cfg : Config} {w w' : World} {sender : Address} {o : Order} {maxPrice value : ℕ}
    (h : fillOrder cfg w sender o maxPrice value = some w') :
    w'.orders = Function.update w.orders o.key ⟨0, 0, 0, false⟩ := by
  unfold fillOrder at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
  simp only [fillBody, orders_setPendingNative, orders_deleteOrder, orders_settleBidBody, orders_payOutBody,
    orders_mint, orders_payOut, orders_settle, orders_transfer, orders_start]
  split_ifs <;> rfl

theorem cancel_orders {cfg : Config} {w w' : World} {sender : Address} {o : Order}
    (h : cancelOrder cfg w sender o = some w') :
    w'.orders = Function.update w.orders o.key ⟨0, 0, 0, false⟩ := by
  unfold cancelOrder at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
  simp [cancelBody, orders_settleBidBody, orders_payOutBody]

theorem liquidityFill_orders {cfg : Config} {w w' : World} {o : Order} {amountOut : ℕ}
    (h : fillFromPoolLiquidity cfg w o amountOut = some w') :
    w'.orders = Function.update w.orders o.key ⟨0, 0, 0, false⟩ := by
  unfold fillFromPoolLiquidity at h; split_ifs at h; simp only [Option.some.injEq] at h; subst h
  simp [liquidityFillBody, orders_settleBidBody, Tx.payOut]
  split_ifs <;> rfl

/-! ## Bridge to the verified partial-fill arithmetic -/

/-- `_reduceAfterMatch` stores exactly `AsyncSwap.Order.reduce` (remaining input, remaining
    minimum, remaining bid) when the order stays open, and deletes it when the reduced order is
    closed.  Hence `AsyncSwapSpec/Reduce.lean`'s cumulative guarantees (input conservation,
    `maker_limit_honored`, bid accounting) hold for the state machine's matches. -/
theorem reduceSideBody_orders (cfg : Config) (t : Tx) (k : OrderKey) (cp : Address) (used received : ℕ) :
    (reduceSideBody cfg t k cp used received).w.orders k =
      if ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).amountIn = 0
         ∨ ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).amountOutMin = 0
      then ⟨0, 0, 0, false⟩
      else ⟨((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).amountIn,
            ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).amountOutMin,
            ((OrderInfo.toSpec k (t.w.orders k)).reduce ⟨used, received⟩).priorityFee,
            (t.w.orders k).escrowed⟩ := by
  simp only [reduceSideBody]
  split_ifs with h <;> simp [orders_settleBidBody, orders_payOutBody]

/-- A match is only executed on an admissible pair, and then the amounts are exactly
    `_matchAmounts`, which honours both limit prices (`AsyncSwap.matchAmounts_sound`). -/
theorem matchLoop_head_sound {cfg : Config} {t t' : Tx} {m : MatchChoice} {ms : List MatchChoice}
    (h : matchLoop cfg t (m :: ms) = some t') :
    matchGuard cfg t.w m.sellKey m.buyKey m.restingBuy ∧
    AsyncSwap.MatchSound (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey))
      (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey))
      (AsyncSwap.matchAmounts (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey))
        (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey)) m.restingBuy) := by
  simp only [matchLoop] at h
  split_ifs at h with hg
  refine ⟨hg, ?_⟩
  obtain ⟨_, _, _, _, _, _, _, ha, hq, _⟩ := hg
  -- positivity of the stored inputs follows from a non-zero match amount
  have hs : 0 < (t.w.orders m.sellKey).amountIn := by
    by_contra h0
    have : (OrderInfo.toSpec m.sellKey (t.w.orders m.sellKey)).amountIn = 0 := by
      simp [OrderInfo.toSpec]; omega
    exact ha (by cases m.restingBuy <;> simp [AsyncSwap.matchAmounts, AsyncSwap.mulDiv, this])
  have hb : 0 < (t.w.orders m.buyKey).amountIn := by
    by_contra h0
    have : (OrderInfo.toSpec m.buyKey (t.w.orders m.buyKey)).amountIn = 0 := by
      simp [OrderInfo.toSpec]; omega
    exact hq (by cases m.restingBuy <;> simp [AsyncSwap.matchAmounts, AsyncSwap.mulDiv, this])
  exact AsyncSwap.matchAmounts_sound _ _ _ hs hb _ rfl ha hq

/-! ## Bids are never refunded -/

/-- `settlePriorityFee` burns exactly the bid from the hook's numeraire claims and credits it to
    the pool (donation) or the vault (forfeit); the maker never receives it. -/
theorem settleBidBody_claims (cfg : Config) (t : Tx) (n : ℕ) :
    (settleBidBody cfg t n).w.claims numeraire cfg.hook = t.w.claims numeraire cfg.hook - n
    ∧ ((settleBidBody cfg t n).w.reserves numeraire + (settleBidBody cfg t n).w.claims numeraire cfg.vault
        = t.w.reserves numeraire + t.w.claims numeraire cfg.vault + n)
    ∧ (∀ a, a ≠ cfg.hook → a ≠ cfg.vault →
        (settleBidBody cfg t n).w.claims numeraire a = t.w.claims numeraire a)
    ∧ (settleBidBody cfg t n).w.bal = t.w.bal := by
  have hhv := cfg.hook_ne_vault
  simp only [settleBidBody]
  split_ifs <;>
    simp [Tx.burn, Tx.mint, Tx.donate, Tx.addDelta, adjust, Function.update_apply, hhv, Ne.symm hhv] <;>
    (try constructor) <;> (try intro a ha hb) <;> simp_all <;> omega

end AsyncSwapProtocol.V2
