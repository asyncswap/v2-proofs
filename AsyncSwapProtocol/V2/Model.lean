import AsyncSwapProtocol.Fee
import AsyncSwapSpec.Match
import AsyncSwapSpec.Reduce

/-!
# AsyncSwap v2 protocol model

Extends the production call-sequence model (`AsyncSwapProtocol/Model.lean`) to the v2 hook
(`asyncswap/v2` `src/`): priority bids, order-to-order matching in the create unlock,
`matchBook`, `fillFromPoolLiquidity`, native proceeds as PoolManager claims and
`NativeClaims.redeem`.  Same conventions: one pool, `currency1` is the numeraire (USDC),
`currency0` may be native, keccak is injective, signatures are an oracle, a transaction is
`Option World` with `none` = revert.

What the v2 contracts add, and where it is modelled:

| Solidity | Here |
| --- | --- |
| `Router.swap`: `priorityFee` must match; `_settlePriorityFee` after input settle; `HOOK.matchNewOrder` | `swapBody` = `createBody` → `priorityFeeBody` → `matchLoop` |
| `AsyncFiller.addOrder` mode / min / max checks | `addOrderGuard` |
| `recordPriorityFee` (`numeraire.take(pm, hook, amount, true)`) | `priorityFeeBody` |
| `settlePriorityFee`: `donate` to active LPs or forfeit to the vault | `settleBidBody` |
| `_transferEscrow`: burn hook claim, pay counterparty (claims if native) | `payOutBody` |
| `_reduceAfterMatch` / `_settleMatchedPriorityFee` | `reduceSideBody`, amounts from `AsyncSwap.Order.reduce` |
| `AsyncMatching._matchAmounts` | `AsyncSwap.matchAmounts` (proved sound in `AsyncSwapSpec/Match.lean`) |
| `fill`, `cancel` with native claims and bid settlement | `fillBody`, `cancelBody` |
| `matchBook(key, maxMatches)` | `matchBook` |
| `fillFromPoolLiquidity` | `liquidityFillBody` (pool output is an input obeying the contract's checks) |
| `NativeClaims.redeem` | `redeemNative` |
| `setOrderingMode` (only with an empty book) | `setOrderingMode` |

Which resting order a match is executed against is an *input* of the action; the protocol
theorems hold for every admissible choice.  That the contract chooses the best price and, at
equal price, the highest bid then the earliest sequence is the book-layer property (roadmap
item 3), not part of this model.
-/

namespace AsyncSwapProtocol.V2

abbrev Address := ℕ
abbrev Currency := Bool

/-- `AsyncOrder` calldata. -/
structure Order where
  owner : Address
  zeroForOne : Bool
  amountIn : ℕ
  amountOutMin : ℕ
  priorityFee : ℕ
  salt : ℕ
  deriving DecidableEq, Repr

structure OrderKey where
  owner : Address
  zeroForOne : Bool
  salt : ℕ
  deriving DecidableEq, Repr

def Order.key (o : Order) : OrderKey := ⟨o.owner, o.zeroForOne, o.salt⟩
def OrderKey.input (k : OrderKey) : Currency := !k.zeroForOne
def OrderKey.output (k : OrderKey) : Currency := k.zeroForOne
/-- A *buy* spends the numeraire (currency1), i.e. `zeroForOne = false`. -/
def OrderKey.isBuy (k : OrderKey) : Bool := !k.zeroForOne
def Order.input (o : Order) : Currency := o.key.input
def Order.output (o : Order) : Currency := o.key.output

/-- `AsyncFiller.OrderInfo` (value-carrying fields). -/
structure OrderInfo where
  amountIn : ℕ
  amountOutMin : ℕ
  priorityFee : ℕ
  escrowed : Bool
  deriving DecidableEq, Repr

/-- The `AsyncSwapSpec` view of a stored order, for `matchAmounts` / `reduce`. -/
def OrderInfo.toSpec (k : OrderKey) (i : OrderInfo) : AsyncSwap.Order :=
  { owner := k.owner, amountIn := i.amountIn, amountOutMin := i.amountOutMin, isBuy := k.isBuy,
    zeroForOne := k.zeroForOne, priorityFee := i.priorityFee, priorityFeeEscrowed := i.escrowed }

inductive SigPayload
  | setExecutor (maker executor : Address) (allow : Bool) (nonce deadline : ℕ)
  | updatePrice (key : OrderKey) (storedAmountIn newAmountOutMin nonce deadline : ℕ)
  | cancel (key : OrderKey) (storedAmountIn nonce deadline : ℕ)
  | permitOrder (owner : Address) (zeroForOne : Bool) (amountIn amountOutMin nonce deadline : ℕ)
  deriving DecidableEq

structure Config where
  router : Address
  hook : Address
  vault : Address
  pm : Address
  /-- `NativeClaims` redemption contract. -/
  nativeClaims : Address
  native0 : Bool
  sigOk : SigPayload → Address → Bool
  router_ne_hook : router ≠ hook
  router_ne_vault : router ≠ vault
  router_ne_pm : router ≠ pm
  hook_ne_vault : hook ≠ vault
  hook_ne_pm : hook ≠ pm
  vault_ne_pm : vault ≠ pm
  nc_ne_pm : nativeClaims ≠ pm
  nc_ne_hook : nativeClaims ≠ hook
  nc_ne_vault : nativeClaims ≠ vault
  nc_ne_router : nativeClaims ≠ router

def Config.isNative (cfg : Config) (c : Currency) : Bool := !c && cfg.native0
/-- The numeraire is currency1. -/
def numeraire : Currency := true

structure World where
  bal : Currency → Address → ℤ
  claims : Currency → Address → ℤ
  /-- Tokens inside the PoolManager owned by the pool itself: LP liquidity and accrued LP fees
      (`donate` lands here).  `bal c pm = Σ claims + reserves` is the backing invariant. -/
  reserves : Currency → ℤ
  /-- `poolManager.getLiquidity(poolId) != 0`. -/
  hasLiquidity : Bool
  /-- `Book.orderingMode == PriorityFee`. -/
  priorityMode : Bool
  orders : OrderKey → OrderInfo
  openKeys : Finset OrderKey
  isExecutor : Address → Address → Bool
  hookNonce : Address → ℕ → Bool
  routerCancelNonce : Address → ℕ → Bool
  permit2Nonce : Address → ℕ → Bool
  owner : Address
  pendingOwner : Address

structure Tx where
  w : World
  delta : Currency → Address → ℤ
  pendingNative : ℕ

def adjust (f : Address → ℤ) (a : Address) (g : ℤ → ℤ) : Address → ℤ := Function.update f a (g (f a))

namespace Tx

def start (w : World) : Tx := ⟨w, fun _ _ => 0, 0⟩

def debit (t : Tx) (c : Currency) (a : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with bal := Function.update t.w.bal c (adjust (t.w.bal c) a (· - n)) } }
def credit (t : Tx) (c : Currency) (a : Address) (n : ℕ) : Tx :=
  { t with w := { t.w with bal := Function.update t.w.bal c (adjust (t.w.bal c) a (· + n)) } }
def transfer (t : Tx) (c : Currency) (src dst : Address) (n : ℕ) : Tx := (t.debit c src n).credit c dst n

def addDelta (t : Tx) (c : Currency) (a : Address) (d : ℤ) : Tx :=
  { t with delta := Function.update t.delta c (adjust (t.delta c) a (· + d)) }

/-- `manager.mint(dst, id, n)`. -/
def mint (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address) : Tx :=
  { (t.addDelta c by_ (-(n : ℤ))) with
    w := { t.w with claims := Function.update t.w.claims c (adjust (t.w.claims c) dst (· + n)) } }
/-- `manager.burn(src, id, n)`. -/
def burn (t : Tx) (c : Currency) (src : Address) (n : ℕ) (by_ : Address) : Tx :=
  { (t.addDelta c by_ (n : ℤ)) with
    w := { t.w with claims := Function.update t.w.claims c (adjust (t.w.claims c) src (· - n)) } }
/-- `manager.take(c, dst, n)` — real tokens out of the PoolManager. -/
def take (cfg : Config) (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (by_ : Address) : Tx :=
  (t.transfer c cfg.pm dst n).addDelta c by_ (-(n : ℤ))
/-- `sync` + transfer `payer → pm` + `settle` / `settleFor(creditTo)`. -/
def settle (cfg : Config) (t : Tx) (c : Currency) (payer creditTo : Address) (n : ℕ) : Tx :=
  (t.transfer c payer cfg.pm n).addDelta c creditTo (n : ℤ)
def accountSwap (t : Tx) (c : Currency) (swapper hook : Address) (n : ℕ) : Tx :=
  (t.addDelta c swapper (-(n : ℤ))).addDelta c hook (n : ℤ)
/-- `manager.donate`: tokens stay in the PoolManager and become the pool's; the caller owes `n`. -/
def donate (t : Tx) (c : Currency) (n : ℕ) (by_ : Address) : Tx :=
  { (t.addDelta c by_ (-(n : ℤ))) with
    w := { t.w with reserves := Function.update t.w.reserves c (t.w.reserves c + n) } }
/-- `manager.swap` from the hook against pool liquidity: the pool takes `amountIn` of `cin`
    and pays `amountOut` of `cout`; the caller's deltas are `-amountIn` / `+amountOut`. -/
def poolSwap (t : Tx) (cin cout : Currency) (amountIn amountOut : ℕ) (by_ : Address) : Tx :=
  { ((t.addDelta cin by_ (-(amountIn : ℤ))).addDelta cout by_ (amountOut : ℤ)) with
    w := { t.w with reserves := Function.update (Function.update t.w.reserves cin (t.w.reserves cin + amountIn))
                                  cout (t.w.reserves cout - amountOut) } }
/-- `take(c, dst, n, claims)` from `CurrencySettler`: real tokens, or claims when `asClaims`. -/
def payOut (cfg : Config) (t : Tx) (c : Currency) (dst : Address) (n : ℕ) (asClaims : Bool) (by_ : Address) : Tx :=
  if asClaims then t.mint c dst n by_ else t.take cfg c dst n by_

def deltasZero (cfg : Config) (t : Tx) : Prop :=
  ∀ c, t.delta c cfg.router = 0 ∧ t.delta c cfg.hook = 0 ∧ t.delta c cfg.vault = 0
       ∧ t.delta c cfg.nativeClaims = 0
instance (cfg : Config) (t : Tx) : Decidable (t.deltasZero cfg) := by unfold deltasZero; infer_instance

def setOrder (t : Tx) (k : OrderKey) (i : OrderInfo) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k i } }
def createOrder (t : Tx) (k : OrderKey) (i : OrderInfo) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k i, openKeys := insert k t.w.openKeys } }
def deleteOrder (t : Tx) (k : OrderKey) : Tx :=
  { t with w := { t.w with orders := Function.update t.w.orders k ⟨0, 0, 0, false⟩,
                           openKeys := t.w.openKeys.erase k } }
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

/-! ## Bodies shared by several entry points -/

namespace Protocol
open Tx

/-- `AsyncFiller.settlePriorityFee(amount)`: donate to active LPs, else forfeit to the vault.
    Either way the hook's numeraire claim is burned. -/
def settleBidBody (cfg : Config) (t : Tx) (amount : ℕ) : Tx :=
  if t.w.hasLiquidity then
    (t.donate numeraire amount cfg.hook).burn numeraire cfg.hook amount cfg.hook
  else
    (t.burn numeraire cfg.hook amount cfg.hook).mint numeraire cfg.vault amount cfg.hook

/-- `_transferEscrow(currency, recipient, amount, hook)`: burn the hook's escrow claim and pay
    the recipient — as claims when the currency is native. -/
def payOutBody (cfg : Config) (t : Tx) (c : Currency) (recipient : Address) (amount : ℕ) : Tx :=
  (t.burn c cfg.hook amount cfg.hook).payOut cfg c recipient amount (cfg.isNative c) cfg.hook

/-- `AsyncFiller.MIN_PRIORITY_FEE` / `MAX_PRIORITY_FEE`. -/
def minBid : ℕ := 100000
def maxBid : ℕ := 2 ^ 64 - 1

/-- `AsyncFiller.addOrder` checks. -/
abbrev addOrderGuard (w : World) (o : Order) : Prop :=
  (w.priorityMode = false → o.priorityFee = 0)
  ∧ (w.priorityMode = true → minBid ≤ o.priorityFee)
  ∧ o.priorityFee ≤ maxBid

/-- `_beforeSwap` + `_createOrder` + `addOrder` + `BeforeSwapDelta` + the router's input settle. -/
def createBody (cfg : Config) (t : Tx) (o : Order) (payer : Address) : Tx :=
  let t1 := t.mint o.input cfg.hook o.amountIn cfg.hook
  let t2 := t1.createOrder o.key ⟨o.amountIn, o.amountOutMin, o.priorityFee, decide (o.priorityFee = 0)⟩
  let t3 := t2.accountSwap o.input cfg.router cfg.hook o.amountIn
  t3.settle cfg o.input payer cfg.router o.amountIn

/-- `Router._settlePriorityFee` + `hook.recordPriorityFee`: the maker's USDC bid is pulled
    into the PoolManager, credited to the hook, and minted as the hook's claim. -/
def priorityFeeBody (cfg : Config) (t : Tx) (o : Order) : Tx :=
  if o.priorityFee = 0 then t else
  let t1 := t.settle cfg numeraire o.owner cfg.hook o.priorityFee
  let t2 := t1.mint numeraire cfg.hook o.priorityFee cfg.hook
  t2.setOrder o.key { t2.w.orders o.key with escrowed := true }

/-! ### One matched side (`_reduceAfterMatch`) -/

/-- One side of a match as the hook sees it: `used` of its input left the escrow to the
    counterparty, `received` of its output arrived. -/
def reduceSideBody (cfg : Config) (t : Tx) (k : OrderKey) (counterparty : Address) (used received : ℕ) : Tx :=
  let i := t.w.orders k
  let spec := OrderInfo.toSpec k i
  let r := spec.reduce ⟨used, received⟩                 -- AsyncSwapSpec: remaining amounts and bid
  let filledBid := spec.donatedFee ⟨used, received⟩      -- `mulDiv(oldFee, used, oldInput)`
  let t1 := payOutBody cfg t k.input counterparty used    -- `_transferEscrow`
  let t2 := settleBidBody cfg t1 filledBid                -- `_settleMatchedPriorityFee`
  if r.amountIn = 0 ∨ r.amountOutMin = 0 then
    -- close: settle the unfilled bid, refund the unused input, delete
    let t3 := settleBidBody cfg t2 r.priorityFee
    let t4 := if r.amountIn = 0 then t3 else payOutBody cfg t3 k.input k.owner r.amountIn
    t4.deleteOrder k
  else
    t2.setOrder k ⟨r.amountIn, r.amountOutMin, r.priorityFee, i.escrowed⟩

/-- `_matchPair(sellKey, buyKey)`: amounts from `_matchAmounts`, then both sides reduced.
    `restingBuy` is whether the buyer is the older order. -/
def matchPairBody (cfg : Config) (t : Tx) (sellKey buyKey : OrderKey) (restingBuy : Bool) : Tx :=
  let m := AsyncSwap.matchAmounts (OrderInfo.toSpec sellKey (t.w.orders sellKey))
                                  (OrderInfo.toSpec buyKey (t.w.orders buyKey)) restingBuy
  let t1 := reduceSideBody cfg t sellKey buyKey.owner m.assetAmount m.quoteAmount
  reduceSideBody cfg t1 buyKey sellKey.owner m.quoteAmount m.assetAmount

/-- Admissibility of one match, as `_matchPair` / `matchIncoming` check it: both open,
    opposite sides, prices cross (the incoming order's price key reaches the resting one),
    bids escrowed, non-zero amounts. -/
abbrev matchGuard (cfg : Config) (w : World) (sellKey buyKey : OrderKey) (restingBuy : Bool) : Prop :=
  sellKey ∈ w.openKeys ∧ buyKey ∈ w.openKeys
  ∧ sellKey.isBuy = false ∧ buyKey.isBuy = true
  ∧ ((w.orders sellKey).priorityFee ≠ 0 → (w.orders sellKey).escrowed = true)
  ∧ ((w.orders buyKey).priorityFee ≠ 0 → (w.orders buyKey).escrowed = true)
  ∧ AsyncSwap.priceKey false (w.orders sellKey).amountIn (w.orders sellKey).amountOutMin
      ≤ AsyncSwap.priceKey true (w.orders buyKey).amountIn (w.orders buyKey).amountOutMin
  ∧ (AsyncSwap.matchAmounts (OrderInfo.toSpec sellKey (w.orders sellKey))
        (OrderInfo.toSpec buyKey (w.orders buyKey)) restingBuy).assetAmount ≠ 0
  ∧ (AsyncSwap.matchAmounts (OrderInfo.toSpec sellKey (w.orders sellKey))
        (OrderInfo.toSpec buyKey (w.orders buyKey)) restingBuy).quoteAmount ≠ 0
  ∧ (cfg.hook ≠ sellKey.owner ∧ cfg.hook ≠ buyKey.owner)

/-- A chosen match: which resting pair, and which side rests. -/
structure MatchChoice where
  sellKey : OrderKey
  buyKey : OrderKey
  restingBuy : Bool
  deriving DecidableEq

/-- `matchIncoming` / `matchBook`: at most `MAX_MATCHES_PER_CALL = 8` matches, each admissible
    in the state it meets. -/
def matchLoop (cfg : Config) : Tx → List MatchChoice → Option Tx
  | t, [] => some t
  | t, m :: ms =>
      if matchGuard cfg t.w m.sellKey m.buyKey m.restingBuy then
        matchLoop cfg (matchPairBody cfg t m.sellKey m.buyKey m.restingBuy) ms
      else none

def maxMatchesPerCall : ℕ := 8

/-! ## Entry points -/

structure UserParams where
  user : Address
  executor : Address
  amountOutMin : ℕ
  priorityFee : ℕ
  deriving DecidableEq

structure PermitData where
  nonce : ℕ
  deadline : ℕ

structure ExecutorGrant where
  present : Bool
  nonce : ℕ
  deadline : ℕ

abbrev createHookGuard (cfg : Config) (w : World) (o : Order) (up : UserParams) : Prop :=
  up.executor = cfg.router ∧ 0 < o.amountIn ∧ w.isExecutor up.user cfg.router = true
  ∧ 0 < up.amountOutMin ∧ (w.orders o.key).amountIn = 0 ∧ addOrderGuard w o

abbrev swapGuard (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) (up : UserParams) : Prop :=
  o.owner = sender ∧ up.user = o.owner ∧ up.executor = cfg.router
  ∧ up.amountOutMin = o.amountOutMin ∧ up.priorityFee = o.priorityFee
  ∧ (if cfg.isNative o.input then value = o.amountIn ∧ (value : ℤ) ≤ w.bal o.input sender
     else value = 0 ∧ (o.amountIn : ℤ) ≤ w.bal o.input o.owner)
  ∧ (o.priorityFee : ℤ) ≤ w.bal numeraire o.owner
  ∧ createHookGuard cfg w o up

/-- `Router.swap` → `unlock` → create → bid escrow → `matchNewOrder` with the book's choices. -/
def swapBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) (ms : List MatchChoice) : Option Tx :=
  let t0 := Tx.start w
  let t1 := if cfg.isNative o.input
            then createBody cfg (t0.transfer o.input sender cfg.router value) o cfg.router
            else createBody cfg t0 o o.owner
  let t2 := priorityFeeBody cfg t1 o
  matchLoop cfg t2 ms

def swap (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) (up : UserParams)
    (ms : List MatchChoice) : Option World :=
  if swapGuard cfg w sender o value up ∧ ms.length ≤ maxMatchesPerCall then
    match swapBody cfg w sender o value ms with
    | some t => if t.deltasZero cfg then some t.w else none
    | none => none
  else none

/-- `Router.matchBook(key, maxMatches)`: anyone continues a crossed book. -/
def matchBook (cfg : Config) (w : World) (maxMatches : ℕ) (ms : List MatchChoice) : Option World :=
  if 0 < maxMatches ∧ maxMatches ≤ maxMatchesPerCall ∧ ms.length ≤ maxMatches then
    match matchLoop cfg (Tx.start w) ms with
    | some t => if t.deltasZero cfg then some t.w else none
    | none => none
  else none

def liveGross (w : World) (k : OrderKey) : ℕ := gross (w.orders k).amountOutMin

abbrev fillGuard (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) : Prop :=
  (if cfg.isNative o.output then value = liveGross w o.key ∧ (value : ℤ) ≤ w.bal o.output sender
   else value = 0 ∧ (liveGross w o.key : ℤ) ≤ w.bal o.output sender)
  ∧ liveGross w o.key ≤ maxPrice
  ∧ w.isExecutor o.owner cfg.router = true
  ∧ (w.orders o.key).amountIn ≠ 0
  ∧ ((w.orders o.key).priorityFee ≠ 0 → (w.orders o.key).escrowed = true)
  ∧ o.key ∈ w.openKeys

/-- `AsyncFiller.fill` (v2): native legs are claims; the whole bid is settled. -/
def fillBody (cfg : Config) (w : World) (sender : Address) (o : Order) (value : ℕ) : Tx :=
  let i := w.orders o.key
  let live := liveGross w o.key
  let fee := poolFee i.amountOutMin
  let t0 := Tx.start w
  let t1 := if cfg.isNative o.output then (t0.transfer o.output sender cfg.hook value).setPendingNative value else t0
  let t2 := if cfg.isNative o.output then t1 else t1.settle cfg o.output sender cfg.hook live
  let t3 := if cfg.isNative o.output then t2.setPendingNative (t2.pendingNative - live) else t2
  let t4 := if cfg.isNative o.output then t3.settle cfg o.output cfg.hook cfg.hook live else t3
  let t5 := t4.payOut cfg o.output o.owner i.amountOutMin (cfg.isNative o.output) cfg.hook
  let t6 := t5.mint o.output cfg.vault fee cfg.hook
  let t7 := payOutBody cfg t6 o.input sender i.amountIn
  let t8 := settleBidBody cfg t7 i.priorityFee
  (t8.deleteOrder o.key).setPendingNative 0

def fillOrder (cfg : Config) (w : World) (sender : Address) (o : Order) (maxPrice value : ℕ) : Option World :=
  if fillGuard cfg w sender o maxPrice value ∧ (fillBody cfg w sender o value).deltasZero cfg
  then some (fillBody cfg w sender o value).w else none

abbrev cancelHookGuard (cfg : Config) (w : World) (o : Order) : Prop :=
  (cfg.router = o.owner ∨ w.isExecutor o.owner cfg.router = true)
  ∧ (w.orders o.key).amountIn ≠ 0
  ∧ ((w.orders o.key).priorityFee ≠ 0 → (w.orders o.key).escrowed = true)
  ∧ o.key ∈ w.openKeys

def cancelBody (cfg : Config) (t : Tx) (o : Order) : Tx :=
  let i := t.w.orders o.key
  let t1 := payOutBody cfg t o.input o.owner i.amountIn
  let t2 := settleBidBody cfg t1 i.priorityFee
  t2.deleteOrder o.key

def cancelOrder (cfg : Config) (w : World) (sender : Address) (o : Order) : Option World :=
  if sender = o.owner ∧ cancelHookGuard cfg w o ∧ (cancelBody cfg (Tx.start w) o).deltasZero cfg
  then some (cancelBody cfg (Tx.start w) o).w else none

abbrev cancelWithSigGuard (cfg : Config) (w : World) (o : Order) (nonce deadline now : ℕ) : Prop :=
  now ≤ deadline ∧ w.routerCancelNonce o.owner nonce = false
  ∧ cfg.sigOk (.cancel o.key (w.orders o.key).amountIn nonce deadline) o.owner = true
  ∧ cancelHookGuard cfg w o

def cancelWithSig (cfg : Config) (w : World) (o : Order) (nonce deadline now : ℕ) : Option World :=
  if cancelWithSigGuard cfg w o nonce deadline now
     ∧ (cancelBody cfg ((Tx.start w).useRouterCancelNonce o.owner nonce) o).deltasZero cfg
  then some (cancelBody cfg ((Tx.start w).useRouterCancelNonce o.owner nonce) o).w else none

/-- `fillFromPoolLiquidity`: the escrow is swapped through the pool; the maker is paid
    `amountOut` (claims if native).  `amountOut` is the pool's result, constrained by the
    contract's own checks (`NoActiveLiquidity`, `PartialLiquidityFill`, `LimitPriceNotMet`). -/
abbrev liquidityFillGuard (cfg : Config) (w : World) (o : Order) (amountOut : ℕ) : Prop :=
  o.key ∈ w.openKeys ∧ (w.orders o.key).amountIn ≠ 0
  ∧ w.hasLiquidity = true
  ∧ (w.orders o.key).amountOutMin ≤ amountOut
  ∧ (amountOut : ℤ) ≤ w.reserves o.output
  ∧ ((w.orders o.key).priorityFee ≠ 0 → (w.orders o.key).escrowed = true)

def liquidityFillBody (cfg : Config) (w : World) (o : Order) (amountOut : ℕ) : Tx :=
  let i := w.orders o.key
  let t0 := Tx.start w
  let t1 := t0.burn o.input cfg.hook i.amountIn cfg.hook                     -- `input.settle(pm, hook, amountIn, true)`
  let t2 := t1.poolSwap o.input o.output i.amountIn amountOut cfg.hook        -- `manager.swap`
  let t3 := t2.payOut cfg o.output o.owner amountOut (cfg.isNative o.output) cfg.hook
  let t4 := settleBidBody cfg t3 i.priorityFee
  t4.deleteOrder o.key

def fillFromPoolLiquidity (cfg : Config) (w : World) (o : Order) (amountOut : ℕ) : Option World :=
  if liquidityFillGuard cfg w o amountOut ∧ (liquidityFillBody cfg w o amountOut).deltasZero cfg
  then some (liquidityFillBody cfg w o amountOut).w else none

/-- `NativeClaims.redeem(amount, recipient)`: burn the caller's native claims, take ETH out. -/
def redeemNative (cfg : Config) (w : World) (sender : Address) (amount : ℕ) (recipient : Address) : Option World :=
  if cfg.native0 = true ∧ recipient ≠ 0 ∧ (amount : ℤ) ≤ w.claims false sender ∧ 0 < amount then
    some (((Tx.start w).burn false sender amount cfg.nativeClaims).take cfg false recipient amount cfg.nativeClaims).w
  else none

abbrev updatePriceGuard (w : World) (caller : Address) (o : Order) (newMin : ℕ) : Prop :=
  caller = o.owner ∧ newMin ≠ 0 ∧ (w.orders o.key).amountIn ≠ 0

def updatePrice (w : World) (sender : Address) (o : Order) (newMin : ℕ) : Option World :=
  if updatePriceGuard w sender o newMin
  then some ((Tx.start w).setOrder o.key { w.orders o.key with amountOutMin := newMin }).w else none

/-- `setOrderingMode`: only while the book is empty. -/
def setOrderingMode (w : World) (sender : Address) (mode : Bool) : Option World :=
  if sender = w.owner ∧ w.openKeys = ∅ then some { w with priorityMode := mode } else none

def setExecutor (w : World) (sender executor : Address) (allow : Bool) : Option World :=
  some ((Tx.start w).setExecutor sender executor allow).w

inductive Action
  | swap (sender : Address) (o : Order) (value : ℕ) (up : UserParams) (ms : List MatchChoice)
  | matchBook (sender : Address) (maxMatches : ℕ) (ms : List MatchChoice)
  | fillOrder (sender : Address) (o : Order) (maxPrice value : ℕ)
  | cancelOrder (sender : Address) (o : Order)
  | cancelWithSig (sender : Address) (o : Order) (nonce deadline now : ℕ)
  | fillFromPoolLiquidity (sender : Address) (o : Order) (amountOut : ℕ)
  | redeemNative (sender : Address) (amount : ℕ) (recipient : Address)
  | updatePrice (sender : Address) (o : Order) (newMin : ℕ)
  | setOrderingMode (sender : Address) (mode : Bool)
  | setExecutor (sender executor : Address) (allow : Bool)

def step (cfg : Config) (w : World) : Action → Option World
  | .swap sender o value up ms => swap cfg w sender o value up ms
  | .matchBook _ maxMatches ms => matchBook cfg w maxMatches ms
  | .fillOrder sender o maxPrice value => fillOrder cfg w sender o maxPrice value
  | .cancelOrder sender o => cancelOrder cfg w sender o
  | .cancelWithSig _ o nonce deadline now => cancelWithSig cfg w o nonce deadline now
  | .fillFromPoolLiquidity _ o amountOut => fillFromPoolLiquidity cfg w o amountOut
  | .redeemNative sender amount recipient => redeemNative cfg w sender amount recipient
  | .updatePrice sender o newMin => updatePrice w sender o newMin
  | .setOrderingMode sender mode => setOrderingMode w sender mode
  | .setExecutor sender executor allow => setExecutor w sender executor allow

end Protocol
end AsyncSwapProtocol.V2
