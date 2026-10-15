import AsyncSwapProtocol.Fee

/-!
# AsyncSwap protocol model

A state model of the production contracts (`packages/protocol/src`, commit `fcf75d4`) built
along the call sequence in the repository README:

* **Router** (`Router.sol`): `swap`, `swapWithSig`, `fillOrder`, `cancelOrder`,
  `cancelWithSig`, and the `unlockCallback` dispatcher with its transient `user` / `maxPrice`
  slots.
* **PoolManager** (Uniswap v4): `unlock`, the per-locker currency *deltas* that must net to
  zero before the unlock returns, ERC-6909 *claims*, `swap` with the hook's
  `BeforeSwapDelta`, `settle` / `settleFor`, `take`, `mint`, `burn`.
* **Hook** (`AsyncSwap.sol`, `AsyncFiller.sol`): `beforeSwap` → `_createOrder`,
  `executeOrder` → `AsyncFiller.fill`, `cancelOrder` → `AsyncFiller.cancel`,
  `updatePrice[WithSig]`, `setExecutor[WithSig]`, `invalidateNonce`, the transient
  `PENDING_NATIVE_DEPOSIT_SLOT` ledger fed by `receive()`, ownership and `sweep`.
* **FeeVault** (`FeeVault.sol`): fee claims and `collect`.
* **Token ledgers**: ERC-20 balances and native ETH of every address, so settlement and
  conservation can be stated.

One pool.  `Currency` is `false` for `currency0` and `true` for `currency1`; `currency0`
may be native ETH (`Config.native0`), `currency1` never is (v4 sorts currencies, and
`address(0)` sorts first).  Order ids are the hash preimage `(owner, zeroForOne, salt)`,
i.e. keccak is modelled as injective.  EIP-712 / ERC-1271 / Permit2 signature validity is an
abstract oracle `Config.sigOk` over the *exact fields each struct hash commits to*.

A transaction is `Option World`: `none` is a revert, which rolls back everything including
the transient slots.  Every transaction is written as *guards* (each `require` / `revert`
the contracts perform, plus the PoolManager's end-of-unlock "all deltas are zero" check) and
a *body* that is the straight-line sequence of state effects.
-/

namespace AsyncSwapProtocol

abbrev Address := ℕ
/-- `false` = currency0, `true` = currency1. -/
abbrev Currency := Bool

/-- `AsyncOrder` calldata (pool key fixed; `sqrtPrice` unused by the hook). -/
structure Order where
  owner : Address
  zeroForOne : Bool
  amountIn : ℕ
  amountOutMin : ℕ
  salt : ℕ
  deriving DecidableEq, Repr

/-- `AsyncOrderLibrary.orderId` preimage `(chainId, poolId, owner, zeroForOne, salt)`. -/
structure OrderKey where
  owner : Address
  zeroForOne : Bool
  salt : ℕ
  deriving DecidableEq, Repr

def Order.key (o : Order) : OrderKey := ⟨o.owner, o.zeroForOne, o.salt⟩
/-- `zeroForOne ⇒ input is currency0`. -/
def Order.input (o : Order) : Currency := !o.zeroForOne
def Order.output (o : Order) : Currency := o.zeroForOne

theorem Order.input_ne_output (o : Order) : o.input ≠ o.output := by
  cases o.zeroForOne <;> simp [Order.input, Order.output]

/-- `AsyncFiller.OrderInfo`; `amountIn = 0` is "no such order". -/
structure OrderInfo where
  amountIn : ℕ
  amountOutMin : ℕ
  deriving DecidableEq, Repr

/-- Exactly the fields each EIP-712 / Permit2 struct hash commits to (`OrderSignatures.sol`). -/
inductive SigPayload
  /-- `SetExecutor(maker, executor, allow, pool, nonce, deadline)` — hook domain. -/
  | setExecutor (maker executor : Address) (allow : Bool) (nonce deadline : ℕ)
  /-- `UpdatePrice(maker, tokenIn, tokenOut, amountIn(stored), newAmountOutMin, orderId, nonce, deadline)` — hook domain. -/
  | updatePrice (key : OrderKey) (storedAmountIn newAmountOutMin nonce deadline : ℕ)
  /-- `CancelOrder(maker, tokenIn, tokenOut, amountIn(stored), orderId, nonce, deadline)` — router domain. -/
  | cancel (key : OrderKey) (storedAmountIn nonce deadline : ℕ)
  /-- Permit2 `PermitWitnessTransferFrom` with the `AsyncOrder` witness (`hashOrder`: no salt). -/
  | permitOrder (owner : Address) (zeroForOne : Bool) (amountIn amountOutMin nonce deadline : ℕ)
  deriving DecidableEq

structure Config where
  router : Address
  hook : Address
  vault : Address
  pm : Address
  /-- currency0 is native ETH. -/
  native0 : Bool
  /-- `SignatureChecker.isValidSignatureNow(signer, digest(payload), sig)` for the submitted bytes. -/
  sigOk : SigPayload → Address → Bool
  router_ne_hook : router ≠ hook
  router_ne_vault : router ≠ vault
  router_ne_pm : router ≠ pm
  hook_ne_vault : hook ≠ vault
  hook_ne_pm : hook ≠ pm
  vault_ne_pm : vault ≠ pm

def Config.isNative (cfg : Config) (c : Currency) : Bool := !c && cfg.native0

/-- Persistent on-chain state. -/
structure World where
  /-- ERC-20 balance (or ETH balance when the currency is native) of every address.  Signed
      so that ledger sums are unconditional; non-negativity is an invariant (`Spec.lean`). -/
  bal : Currency → Address → ℤ
  /-- PoolManager ERC-6909 claim balances. -/
  claims : Currency → Address → ℤ
  /-- Hook: `asyncOrders[pool].orders`. -/
  orders : OrderKey → OrderInfo
  /-- Ghost: the keys with `amountIn ≠ 0`, for stating sums over open orders. -/
  openKeys : Finset OrderKey
  /-- Hook: `asyncOrders[pool].isExecutor[maker][executor]`. -/
  isExecutor : Address → Address → Bool
  /-- Hook: `nonceUsed[maker][nonce]` (signed `setExecutor` / `updatePrice`). -/
  hookNonce : Address → ℕ → Bool
  /-- Router: `cancelNonceUsed[maker][nonce]`. -/
  routerCancelNonce : Address → ℕ → Bool
  /-- Permit2 unordered nonces for the maker's signed creates. -/
  permit2Nonce : Address → ℕ → Bool
  owner : Address
  pendingOwner : Address

/-- Transaction-scoped state: the world plus the transient slots that die with the tx. -/
structure Tx where
  w : World
  /-- PoolManager currency deltas per locker (`_accountDelta`). -/
  delta : Currency → Address → ℤ
  /-- Hook `PENDING_NATIVE_DEPOSIT_SLOT`. -/
  pendingNative : ℕ

def adjust (f : Address → ℤ) (a : Address) (g : ℤ → ℤ) : Address → ℤ :=
  Function.update f a (g (f a))

namespace Tx

def start (w : World) : Tx := ⟨w, fun _ _ => 0, 0⟩

/-! ### Token ledger -/

def debit (t : Tx) (c : Currency) (a : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with bal := Function.update t.w.bal c (adjust (t.w.bal c) a (· - n)) } }

def credit (t : Tx) (c : Currency) (a : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with bal := Function.update t.w.bal c (adjust (t.w.bal c) a (· + n)) } }

/-- `transfer` / `transferFrom` / ETH value transfer. -/
def transfer (t : Tx) (c : Currency) (src dst : Address) (n : ℕ) : Tx :=
  (t.debit c src n).credit c dst n

/-! ### PoolManager primitives (the `by` argument is `msg.sender` seen by the PoolManager) -/

def addDelta (t : Tx) (c : Currency) (a : Address) (d : ℤ) : Tx :=
  { t with delta := Function.update t.delta c (adjust (t.delta c) a (· + d)) }

/-- `manager.mint(to, id, n)`: ERC-6909 claims minted, locker owes `n`. -/
def mint (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address) : Tx :=
  { (t.addDelta c by_ (-(n : ℤ))) with
    w := { t.w with claims := Function.update t.w.claims c (adjust (t.w.claims c) dst (· + n)) } }

/-- `manager.burn(from, id, n)`: claims burned, locker credited `n`. -/
def burn (t : Tx) (c : Currency) (src : Address) (n : ℕ) (by_ : Address) : Tx :=
  { (t.addDelta c by_ (n : ℤ)) with
    w := { t.w with claims := Function.update t.w.claims c (adjust (t.w.claims c) src (· - n)) } }

/-- `manager.take(currency, to, n)`: PoolManager pays real tokens out, locker owes `n`. -/
def take (cfg : Config) (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address) : Tx :=
  (t.transfer c cfg.pm dst n).addDelta c by_ (-(n : ℤ))

/-- `sync` + token transfer `payer → PoolManager` + `settle` (credits the caller) or
    `settleFor(creditTo)`.  Native `settle{value: n}` is the same with `payer = caller`. -/
def settle (cfg : Config) (t : Tx) (c : Currency) (payer creditTo : Address) (n : ℕ) : Tx :=
  (t.transfer c payer cfg.pm n).addDelta c creditTo (n : ℤ)

/-- `PoolManager.swap` accounting for a hook that consumes the whole exact input through
    `BeforeSwapDelta`: the swapper owes `n`, the hook is credited `n`. -/
def accountSwap (t : Tx) (c : Currency) (swapper hook : Address) (n : ℕ) : Tx :=
  (t.addDelta c swapper (-(n : ℤ))).addDelta c hook (n : ℤ)

/-- End of `unlock`: every locker's delta must be zero or the PoolManager reverts
    (`CurrencyNotSettled`).  The lockers in this protocol are the router, the hook and the vault. -/
def deltasZero (cfg : Config) (t : Tx) : Prop :=
  ∀ c, t.delta c cfg.router = 0 ∧ t.delta c cfg.hook = 0 ∧ t.delta c cfg.vault = 0

instance (cfg : Config) (t : Tx) : Decidable (t.deltasZero cfg) := by
  unfold deltasZero; infer_instance

/-! ### Hook storage -/

def createOrder (t : Tx) (k : OrderKey) (info : OrderInfo) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k info,
                           openKeys := insert k t.w.openKeys } }

def deleteOrder (t : Tx) (k : OrderKey) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k ⟨0, 0⟩,
                           openKeys := t.w.openKeys.erase k } }

def setMinimum (t : Tx) (k : OrderKey) (newMin : ℕ) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k ⟨(t.w.orders k).amountIn, newMin⟩ } }

def setExecutor (t : Tx) (maker executor : Address) (allow : Bool) : Tx :=
  { t with w := { t.w with
      isExecutor := (Function.update t.w.isExecutor maker (Function.update (t.w.isExecutor maker) executor allow)) } }

def useHookNonce (t : Tx) (maker : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with
      hookNonce := (Function.update t.w.hookNonce maker (Function.update (t.w.hookNonce maker) n true)) } }

def useRouterCancelNonce (t : Tx) (maker : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with
      routerCancelNonce := (Function.update t.w.routerCancelNonce maker (Function.update (t.w.routerCancelNonce maker) n true)) } }

def usePermit2Nonce (t : Tx) (maker : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with
      permit2Nonce := (Function.update t.w.permit2Nonce maker (Function.update (t.w.permit2Nonce maker) n true)) } }

def setPendingNative (t : Tx) (n : ℕ) : Tx := { t with pendingNative := n }

end Tx

/-! ## Transactions -/

/-- `AsyncSwap.UserParams` passed as `hookData`. -/
structure UserParams where
  user : Address
  executor : Address
  amountOutMin : ℕ
  deriving DecidableEq

/-- Signed-create extras: Permit2 `(nonce, deadline)` and an optional `SetExecutor` grant. -/
structure PermitData where
  nonce : ℕ
  deadline : ℕ

structure ExecutorGrant where
  present : Bool
  nonce : ℕ
  deadline : ℕ

/-- Every externally callable action in the sequence diagram. `sender` is `msg.sender`,
    `value` is `msg.value`, `now` is `block.timestamp`. -/
inductive Action
  | swap (sender : Address) (o : Order) (value : ℕ) (up : UserParams)
  | swapWithSig (sender : Address) (o : Order) (permit : PermitData) (grant : ExecutorGrant) (now : ℕ)
  | fillOrder (sender : Address) (o : Order) (maxPrice value : ℕ)
  | cancelOrder (sender : Address) (o : Order)
  | cancelWithSig (sender : Address) (o : Order) (nonce deadline now : ℕ)
  | updatePrice (sender : Address) (o : Order) (newAmountOutMin : ℕ)
  | updatePriceWithSig (sender : Address) (o : Order) (newAmountOutMin nonce deadline now : ℕ)
  | setExecutor (sender executor : Address) (allow : Bool)
  | setExecutorWithSig (sender maker executor : Address) (allow : Bool) (nonce deadline now : ℕ)
  | invalidateNonce (sender : Address) (nonce : ℕ)
  | collectFees (sender : Address) (c : Currency) (recipient : Address)
  | transferOwnership (sender newOwner : Address)
  | acceptOwnership (sender : Address)
  | sweep (sender : Address) (c : Currency) (dst : Address)

/-- Which order a maker-facing action addresses. -/
def Action.key : Action → Option OrderKey
  | .swap _ o _ _ => some o.key
  | .swapWithSig _ o _ _ _ => some o.key
  | .fillOrder _ o _ _ => some o.key
  | .cancelOrder _ o => some o.key
  | .cancelWithSig _ o _ _ _ => some o.key
  | .updatePrice _ o _ => some o.key
  | .updatePriceWithSig _ o _ _ _ _ => some o.key
  | _ => none

def Action.isCreate : Action → Bool
  | .swap .. | .swapWithSig .. => true
  | _ => false

def Action.isClose : Action → Bool
  | .fillOrder .. | .cancelOrder .. | .cancelWithSig .. => true
  | _ => false

def Action.isReprice : Action → Bool
  | .updatePrice .. | .updatePriceWithSig .. => true
  | _ => false

namespace Protocol

open Tx

/-! ### Create: `Router.swap` → `unlock` → `PoolManager.swap` → `beforeSwap` → settle input -/

/-- Hook-side checks shared by both create paths (`_beforeSwap` + `_createOrder`). The salt slot
    being free models the result of the hook's collision walk. -/
abbrev createHookGuard (cfg : Config) (w : World) (o : Order) (up : UserParams) : Prop :=
  up.executor = cfg.router                       -- `sender != hookData.executor` ⇒ revert; sender is the router
  ∧ 0 < o.amountIn                               -- exact input, non-zero
  ∧ w.isExecutor up.user cfg.router = true       -- maker must have granted the router
  ∧ 0 < up.amountOutMin
  ∧ (w.orders o.key).amountIn = 0                -- fresh id (collision walk)

/-- The in-unlock effects of a create, after the maker's input has reached the payer. -/
def createBody (cfg : Config) (t : Tx) (o : Order) (info : OrderInfo) (payer : Address) : Tx :=
  let t1 := t.mint o.input cfg.hook o.amountIn cfg.hook            -- `specified.take(pm, hook, amountIn, true)`
  let t2 := t1.createOrder o.key info                              -- `state.orders[id] = ...`
  let t3 := t2.accountSwap o.input cfg.router cfg.hook o.amountIn  -- `BeforeSwapDelta` accounting
  t3.settle cfg o.input payer cfg.router o.amountIn                -- router settles the maker's input

abbrev swapGuard (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ)
    (up : UserParams) : Prop :=
  o.owner = sender
  ∧ up.user = o.owner ∧ up.executor = cfg.router ∧ up.amountOutMin = o.amountOutMin
  ∧ (if cfg.isNative o.input then value = o.amountIn ∧ (value : ℤ) ≤ w.bal o.input sender
     else value = 0 ∧ (o.amountIn : ℤ) ≤ w.bal o.input o.owner)
  ∧ createHookGuard cfg w o up

def swapBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) : Tx :=
  let t0 := Tx.start w
  if cfg.isNative o.input then
    -- the router holds the maker's ETH, then pays it into the PoolManager itself
    createBody cfg (t0.transfer o.input sender cfg.router value) o ⟨o.amountIn, o.amountOutMin⟩ cfg.router
  else
    createBody cfg t0 o ⟨o.amountIn, o.amountOutMin⟩ o.owner

def swap (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) (up : UserParams) :
    Option World :=
  if swapGuard cfg w sender o value up ∧ (swapBody cfg w sender o value).deltasZero cfg
  then some (swapBody cfg w sender o value).w else none

/-! ### Signed create: `Router.swapWithSig` (ERC-20 input only, Permit2 witness transfer) -/

def grantNeeded (cfg : Config) (w : World) (o : Order) (g : ExecutorGrant) : Bool :=
  g.present && !w.isExecutor o.owner cfg.router

abbrev swapWithSigGuard (cfg : Config) (w : World) (o : Order) (p : PermitData) (g : ExecutorGrant)
    (now : ℕ) : Prop :=
  cfg.isNative o.input = false
  ∧ (grantNeeded cfg w o g = true →
       now ≤ g.deadline ∧ w.hookNonce o.owner g.nonce = false
       ∧ cfg.sigOk (.setExecutor o.owner cfg.router true g.nonce g.deadline) o.owner = true)
  -- the executor check in `_createOrder` sees the grant applied just above
  ∧ (grantNeeded cfg w o g = true ∨ w.isExecutor o.owner cfg.router = true)
  ∧ 0 < o.amountIn ∧ 0 < o.amountOutMin ∧ (w.orders o.key).amountIn = 0
  -- Permit2: signature over the transfer and the order witness, nonce fresh, deadline, funds
  ∧ now ≤ p.deadline ∧ w.permit2Nonce o.owner p.nonce = false
  ∧ cfg.sigOk (.permitOrder o.owner o.zeroForOne o.amountIn o.amountOutMin p.nonce p.deadline) o.owner = true
  ∧ (o.amountIn : ℤ) ≤ w.bal o.input o.owner

def swapWithSigBody (cfg : Config) (w : World) (o : Order) (p : PermitData) (g : ExecutorGrant) : Tx :=
  let t0 := Tx.start w
  let t1 := if grantNeeded cfg w o g then
              (t0.useHookNonce o.owner g.nonce).setExecutor o.owner cfg.router true
            else t0
  let t2 := t1.usePermit2Nonce o.owner p.nonce
  createBody cfg t2 o ⟨o.amountIn, o.amountOutMin⟩ o.owner

def swapWithSig (cfg : Config) (w : World) (o : Order) (p : PermitData) (g : ExecutorGrant) (now : ℕ) :
    Option World :=
  if swapWithSigGuard cfg w o p g now ∧ (swapWithSigBody cfg w o p g).deltasZero cfg
  then some (swapWithSigBody cfg w o p g).w else none

/-! ### Fill: `Router.fillOrder` → `unlock` → pay gross output → `executeOrder` → `AsyncFiller.fill` -/

/-- Live gross price read from hook storage: stored minimum plus `calculatePoolFee`. -/
def liveGross (w : World) (k : OrderKey) : ℕ := gross (w.orders k).amountOutMin

abbrev fillGuard (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) : Prop :=
  -- Router.fillOrder: msg.value rule, native deposit forwarded to the hook
  (if cfg.isNative o.output then value = liveGross w o.key ∧ (value : ℤ) ≤ w.bal o.output sender
   else value = 0 ∧ (liveGross w o.key : ℤ) ≤ w.bal o.output sender)
  -- unlockCallback: live price vs. the filler's cap
  ∧ liveGross w o.key ≤ maxPrice
  -- executeOrder (native): only the same-tx deposit may be spent — `pending ≥ live`, which the
  -- router's `msg.value == livePrice` check makes exact
  -- AsyncFiller.fill
  ∧ w.isExecutor o.owner cfg.router = true
  ∧ (w.orders o.key).amountIn ≠ 0
  ∧ ((w.orders o.key).amountIn : ℤ) ≤ w.claims o.input cfg.hook                       -- `burn` of the escrow claim
  ∧ ((w.orders o.key).amountOutMin : ℤ) ≤ w.bal o.output cfg.pm + liveGross w o.key   -- `take` to the maker
  ∧ ((w.orders o.key).amountIn : ℤ) ≤ w.bal o.input cfg.pm                            -- `take` to the filler

def fillBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) : Tx :=
  let info := w.orders o.key
  let live := liveGross w o.key
  let fee := poolFee info.amountOutMin
  let t0 := Tx.start w
  -- Router.fillOrder: native output is forwarded to the hook before unlock; `receive()` logs it
  let t1 := if cfg.isNative o.output then (t0.transfer o.output sender cfg.hook value).setPendingNative value
            else t0
  -- unlockCallback: ERC-20 output `sync` + `transferFrom(filler, pm, live)` + `settleFor(hook)`
  let t2 := if cfg.isNative o.output then t1 else t1.settle cfg o.output sender cfg.hook live
  -- executeOrder: consume the native ledger
  let t3 := if cfg.isNative o.output then t2.setPendingNative (t2.pendingNative - live) else t2
  -- AsyncFiller.fill
  let t4 := t3.deleteOrder o.key
  let t5 := if cfg.isNative o.output then t4.settle cfg o.output cfg.hook cfg.hook live else t4  -- `output.settle(pm, hook, min+fee, false)`
  let t6 := t5.take cfg o.output o.owner info.amountOutMin cfg.hook                       -- maker paid
  -- `if (fee != 0)` in the contract only skips the event; minting zero claims is a no-op
  let t7 := t6.mint o.output cfg.vault fee cfg.hook                                       -- fee claim to the vault
  let t8 := t7.burn o.input cfg.hook info.amountIn cfg.hook                               -- escrow claim burned
  let t9 := t8.take cfg o.input sender info.amountIn cfg.hook                             -- filler paid
  t9.setPendingNative 0                                                                   -- transient cleared

def fillOrder (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) :
    Option World :=
  if fillGuard cfg w sender o maxPrice value ∧ (fillBody cfg w sender o value).deltasZero cfg
  then some (fillBody cfg w sender o value).w else none

/-! ### Cancel: `Router.cancelOrder` / `cancelWithSig` → `unlock` → `hook.cancelOrder` -/

/-- `AsyncFiller.cancel` with `executor = router`. -/
abbrev cancelHookGuard (cfg : Config) (w : World) (o : Order) : Prop :=
  (cfg.router = o.owner ∨ w.isExecutor o.owner cfg.router = true)
  ∧ (w.orders o.key).amountIn ≠ 0
  ∧ ((w.orders o.key).amountIn : ℤ) ≤ w.claims o.input cfg.hook
  ∧ ((w.orders o.key).amountIn : ℤ) ≤ w.bal o.input cfg.pm

def cancelBody (cfg : Config) (t : Tx) (o : Order) : Tx :=
  let amountIn := (t.w.orders o.key).amountIn
  let t1 := t.deleteOrder o.key
  let t2 := t1.burn o.input cfg.hook amountIn cfg.hook
  t2.take cfg o.input o.owner amountIn cfg.hook

def cancelOrder (cfg : Config) (w : World) (sender : Address) (o : Order) : Option World :=
  if sender = o.owner ∧ cancelHookGuard cfg w o ∧ (cancelBody cfg (Tx.start w) o).deltasZero cfg
  then some (cancelBody cfg (Tx.start w) o).w else none

abbrev cancelWithSigGuard (cfg : Config) (w : World) (o : Order) (nonce deadline now : ℕ) : Prop :=
  now ≤ deadline
  ∧ w.routerCancelNonce o.owner nonce = false
  ∧ cfg.sigOk (.cancel o.key (w.orders o.key).amountIn nonce deadline) o.owner = true
  ∧ cancelHookGuard cfg w o

def cancelWithSigBody (cfg : Config) (w : World) (o : Order) (nonce : ℕ) : Tx :=
  cancelBody cfg ((Tx.start w).useRouterCancelNonce o.owner nonce) o

def cancelWithSig (cfg : Config) (w : World) (o : Order) (nonce deadline now : ℕ) : Option World :=
  if cancelWithSigGuard cfg w o nonce deadline now ∧ (cancelWithSigBody cfg w o nonce).deltasZero cfg
  then some (cancelWithSigBody cfg w o nonce).w else none

/-! ### Reprice: direct call to the hook, no unlock -/

abbrev updatePriceGuard (w : World) (caller : Address) (o : Order) (newMin : ℕ) : Prop :=
  caller = o.owner ∧ newMin ≠ 0 ∧ (w.orders o.key).amountIn ≠ 0

def updatePrice (w : World) (sender : Address) (o : Order) (newMin : ℕ) : Option World :=
  if updatePriceGuard w sender o newMin then some ((Tx.start w).setMinimum o.key newMin).w else none

def updatePriceWithSig (cfg : Config) (w : World) (o : Order) (newMin nonce deadline now : ℕ) :
    Option World :=
  if now ≤ deadline ∧ w.hookNonce o.owner nonce = false
     ∧ cfg.sigOk (.updatePrice o.key (w.orders o.key).amountIn newMin nonce deadline) o.owner = true
     ∧ updatePriceGuard w o.owner o newMin
  then some (((Tx.start w).useHookNonce o.owner nonce).setMinimum o.key newMin).w else none

/-! ### Executor grants and nonces -/

def setExecutor (w : World) (sender executor : Address) (allow : Bool) : Option World :=
  some ((Tx.start w).setExecutor sender executor allow).w

def setExecutorWithSig (cfg : Config) (w : World) (maker executor : Address) (allow : Bool)
    (nonce deadline now : ℕ) : Option World :=
  if now ≤ deadline ∧ w.hookNonce maker nonce = false
     ∧ cfg.sigOk (.setExecutor maker executor allow nonce deadline) maker = true
  then some (((Tx.start w).useHookNonce maker nonce).setExecutor maker executor allow).w else none

def invalidateNonce (w : World) (sender : Address) (nonce : ℕ) : Option World :=
  if w.hookNonce sender nonce = false then some ((Tx.start w).useHookNonce sender nonce).w else none

/-! ### FeeVault.collect: owner-only, `unlock` from the vault, burn and take all fee claims -/

def collectBody (cfg : Config) (w : World) (c : Currency) (recipient : Address) : Tx :=
  -- `if (amount != 0)` in the contract only skips the calls; burning / taking zero is a no-op
  ((Tx.start w).burn c cfg.vault (w.claims c cfg.vault).toNat cfg.vault).take cfg c recipient
    (w.claims c cfg.vault).toNat cfg.vault

def collectFees (cfg : Config) (w : World) (sender : Address) (c : Currency) (recipient : Address) :
    Option World :=
  if sender = w.owner ∧ recipient ≠ 0 ∧ w.claims c cfg.vault ≤ w.bal c cfg.pm
     ∧ (collectBody cfg w c recipient).deltasZero cfg
  then some (collectBody cfg w c recipient).w else none

/-! ### Ownership and sweep -/

def transferOwnership (w : World) (sender newOwner : Address) : Option World :=
  if sender = w.owner ∧ newOwner ≠ 0 then some { w with pendingOwner := newOwner } else none

def acceptOwnership (w : World) (sender : Address) : Option World :=
  if sender = w.pendingOwner then some { w with owner := sender, pendingOwner := 0 } else none

/-- `sweep`: moves the hook's *own* token balance (never claims) to `to`. -/
def sweep (cfg : Config) (w : World) (sender : Address) (c : Currency) (dst : Address) : Option World :=
  if sender = w.owner ∧ dst ≠ 0
  then some ((Tx.start w).transfer c cfg.hook dst (w.bal c cfg.hook).toNat).w else none

/-- The protocol as a transition system. -/
def step (cfg : Config) (w : World) : Action → Option World
  | .swap sender o value up => swap cfg w sender o value up
  | .swapWithSig _ o p g now => swapWithSig cfg w o p g now
  | .fillOrder sender o maxPrice value => fillOrder cfg w sender o maxPrice value
  | .cancelOrder sender o => cancelOrder cfg w sender o
  | .cancelWithSig _ o nonce deadline now => cancelWithSig cfg w o nonce deadline now
  | .updatePrice sender o newMin => updatePrice w sender o newMin
  | .updatePriceWithSig _ o newMin nonce deadline now => updatePriceWithSig cfg w o newMin nonce deadline now
  | .setExecutor sender executor allow => setExecutor w sender executor allow
  | .setExecutorWithSig _ maker executor allow nonce deadline now =>
      setExecutorWithSig cfg w maker executor allow nonce deadline now
  | .invalidateNonce sender nonce => invalidateNonce w sender nonce
  | .collectFees sender c recipient => collectFees cfg w sender c recipient
  | .transferOwnership sender newOwner => transferOwnership w sender newOwner
  | .acceptOwnership sender => acceptOwnership w sender
  | .sweep sender c dst => sweep cfg w sender c dst

end Protocol
end AsyncSwapProtocol
