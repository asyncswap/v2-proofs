import AsyncSwapSpec.Order

/-!
# EIP-712 / Permit2 hashing model (`OrderSignatures.sol`, `_verify`, `cancelWithSig`, `swapWithSig`)

Every `keccak256` on the signed-action paths is applied to one of three kinds of preimage:
a type string (`keccak256("AsyncOrder(...)")`), an `abi.encode` of 32-byte words, or the
EIP-712 envelope `"\x19\x01" ‖ domainSeparator ‖ structHash`. We model `keccak256` as an
arbitrary function on these symbolic preimages that is **collision-free** (`Model.injective`):
this is the only property of the hash the contracts rely on, and it is the standard way to
reason about EIP-712 binding without a concrete Keccak.

The definitions below are transcriptions of `OrderSignatures.sol`, `AsyncOrderLibrary.orderId`,
OpenZeppelin's `EIP712._hashTypedDataV4` and Permit2's `PermitHash.hashWithWitness`. The theorems
say which fields a signature binds (witness binding), that no struct hash of one type can equal
a struct hash of another (type separation), that no digest of one contract's domain can equal a
digest of another's (domain separation), and what an order id determines.
-/

namespace AsyncSwap
namespace Hashing

/-- Symbolic preimages of `keccak256`. -/
inductive Enc
  /-- `keccak256("<type string>")`. -/
  | str (s : String)
  /-- `keccak256(abi.encode(w₀, w₁, …))`; addresses, bools and `bytes32` are words. -/
  | tuple (ws : List ℕ)
  /-- `keccak256("\x19\x01" ‖ domainSeparator ‖ structHash)` (EIP-712 envelope). -/
  | typed (domainSeparator structHash : ℕ)
  deriving DecidableEq

/-- A hash model: `keccak256` on symbolic preimages, assumed collision-free. -/
structure Model where
  keccak : Enc → ℕ
  injective : Function.Injective keccak

/-- `uint256(bool)`. -/
def boolWord (b : Bool) : ℕ := if b then 1 else 0

theorem boolWord_inj {b b' : Bool} (h : boolWord b = boolWord b') : b = b' := by
  cases b <;> cases b' <;> simp [boolWord] at h ⊢

/-- Uniswap v4 `PoolKey`. -/
structure PoolKey where
  currency0 : Address
  currency1 : Address
  fee : ℕ
  tickSpacing : ℕ
  hooks : Address
  deriving DecidableEq

/-- `AsyncOrder` (`src/types/AsyncOrder.sol`). -/
structure AsyncOrder where
  key : PoolKey
  owner : Address
  zeroForOne : Bool
  amountIn : ℕ
  amountOutMin : ℕ
  priorityFee : ℕ
  sqrtPrice : ℕ
  salt : ℕ
  deriving DecidableEq

/-- `OrderSignatures.tokens`: `(tokenIn, tokenOut)` by direction. -/
def AsyncOrder.tokens (o : AsyncOrder) : Address × Address :=
  if o.zeroForOne then (o.key.currency0, o.key.currency1) else (o.key.currency1, o.key.currency0)

/-! ## Type strings, exactly as in `OrderSignatures.sol` -/

def POOL_KEY_TYPE : String :=
  "PoolKey(address currency0,address currency1,uint24 fee,int24 tickSpacing,address hooks)"
def ASYNC_ORDER_TYPE : String :=
  "AsyncOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 amountOutMin,uint256 priorityFee,PoolKey pool)"
def SET_EXECUTOR_TYPE : String :=
  "SetExecutor(address maker,address executor,bool allow,PoolKey pool,uint256 nonce,uint256 deadline)"
def UPDATE_PRICE_TYPE : String :=
  "UpdatePrice(address maker,address tokenIn,address tokenOut,uint256 amountIn,uint256 newAmountOutMin,bytes32 orderId,uint256 nonce,uint256 deadline)"
def CANCEL_ORDER_TYPE : String :=
  "CancelOrder(address maker,address tokenIn,address tokenOut,uint256 amountIn,bytes32 orderId,uint256 nonce,uint256 deadline)"
def TOKEN_PERMISSIONS_TYPE : String := "TokenPermissions(address token,uint256 amount)"
/-- `OrderSignatures.PERMIT2_WITNESS_TYPE`, the string Permit2 appends to its own type. -/
def PERMIT2_WITNESS_TYPE : String :=
  "AsyncOrder witness)" ++ ASYNC_ORDER_TYPE ++ POOL_KEY_TYPE ++ TOKEN_PERMISSIONS_TYPE
/-- Permit2 `PermitHash._PERMIT_TRANSFER_FROM_WITNESS_TYPEHASH_STUB ‖ witnessTypeString`. -/
def PERMIT_WITNESS_TRANSFER_FROM_TYPE : String :=
  "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline," ++
    PERMIT2_WITNESS_TYPE
def EIP712_DOMAIN_TYPE : String :=
  "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"

variable (M : Model)

def poolKeyTypehash : ℕ := M.keccak (.str POOL_KEY_TYPE)
/-- `keccak256(abi.encodePacked(ASYNC_ORDER_TYPE, POOL_KEY_TYPE))`. -/
def asyncOrderTypehash : ℕ := M.keccak (.str (ASYNC_ORDER_TYPE ++ POOL_KEY_TYPE))
def setExecutorTypehash : ℕ := M.keccak (.str (SET_EXECUTOR_TYPE ++ POOL_KEY_TYPE))
def updatePriceTypehash : ℕ := M.keccak (.str UPDATE_PRICE_TYPE)
def cancelOrderTypehash : ℕ := M.keccak (.str CANCEL_ORDER_TYPE)
def tokenPermissionsTypehash : ℕ := M.keccak (.str TOKEN_PERMISSIONS_TYPE)
def permitWitnessTypehash : ℕ := M.keccak (.str PERMIT_WITNESS_TRANSFER_FROM_TYPE)
def eip712DomainTypehash : ℕ := M.keccak (.str EIP712_DOMAIN_TYPE)

/-! ## Struct hashes (`OrderSignatures.sol`) -/

/-- `hashPoolKey`. -/
def hashPoolKey (k : PoolKey) : ℕ :=
  M.keccak (.tuple [poolKeyTypehash M, k.currency0, k.currency1, k.fee, k.tickSpacing, k.hooks])

/-- `hashOrder`: the Permit2 witness. Covers maker, both tokens, the amounts, the bid and the
    pool; **not** `sqrtPrice` (never read by v4) nor `salt` (assigned by the hook). -/
def hashOrder (o : AsyncOrder) : ℕ :=
  M.keccak (.tuple [asyncOrderTypehash M, o.owner, o.tokens.1, o.tokens.2, o.amountIn, o.amountOutMin,
    o.priorityFee, hashPoolKey M o.key])

/-- `hashSetExecutor`. -/
def hashSetExecutor (k : PoolKey) (maker executor : Address) (allow : Bool) (nonce deadline : ℕ) : ℕ :=
  M.keccak (.tuple [setExecutorTypehash M, maker, executor, boolWord allow, hashPoolKey M k, nonce, deadline])

/-- `hashUpdatePrice` (`amountIn` is the stored input, read by the hook). -/
def hashUpdatePrice (o : AsyncOrder) (orderId amountIn newAmountOutMin nonce deadline : ℕ) : ℕ :=
  M.keccak (.tuple [updatePriceTypehash M, o.owner, o.tokens.1, o.tokens.2, amountIn, newAmountOutMin, orderId,
    nonce, deadline])

/-- `hashCancel`. -/
def hashCancel (o : AsyncOrder) (orderId amountIn nonce deadline : ℕ) : ℕ :=
  M.keccak (.tuple [cancelOrderTypehash M, o.owner, o.tokens.1, o.tokens.2, amountIn, orderId, nonce, deadline])

/-! ## EIP-712 domains and digests -/

/-- An EIP-712 domain (`EIP712Domain(name, version, chainId, verifyingContract)`). -/
structure Domain where
  name : String
  version : String
  chainId : ℕ
  verifyingContract : Address
  deriving DecidableEq

/-- OpenZeppelin `_domainSeparatorV4`. -/
def domainSeparator (d : Domain) : ℕ :=
  M.keccak (.tuple [eip712DomainTypehash M, M.keccak (.str d.name), M.keccak (.str d.version), d.chainId,
    d.verifyingContract])

/-- OpenZeppelin `_hashTypedDataV4`: the digest a wallet signs. -/
def digest (d : Domain) (structHash : ℕ) : ℕ := M.keccak (.typed (domainSeparator M d) structHash)

/-! ## Permit2 witness transfer (`PermitHash.hashWithWitness`) -/

/-- `keccak256(abi.encode(_TOKEN_PERMISSIONS_TYPEHASH, token, amount))`. -/
def hashTokenPermissions (token amount : ℕ) : ℕ :=
  M.keccak (.tuple [tokenPermissionsTypehash M, token, amount])

/-- The struct hash Permit2 signs over for `permitWitnessTransferFrom` with our witness type. -/
def permitWitnessStructHash (token amount spender nonce deadline witness : ℕ) : ℕ :=
  M.keccak (.tuple [permitWitnessTypehash M, hashTokenPermissions M token amount, spender, nonce, deadline, witness])

/-- What `Router._settleWithPermit` asks Permit2 to verify: the order's input token for exactly
    `amountIn`, spender = Router, witness = `hashOrder(order)`. -/
def routerPermitStructHash (router : Address) (o : AsyncOrder) (nonce deadline : ℕ) : ℕ :=
  permitWitnessStructHash M o.tokens.1 o.amountIn router nonce deadline (hashOrder M o)

/-! ## Order ids -/

/-- `PoolKey.toId` = `keccak256(abi.encode(key))`. -/
def poolId (k : PoolKey) : ℕ := M.keccak (.tuple [k.currency0, k.currency1, k.fee, k.tickSpacing, k.hooks])

/-- `AsyncOrderLibrary.orderId` = `Router._orderId` = the id `_createOrder` assigns:
    `keccak256(abi.encode(chainId, poolId, owner, zeroForOne, salt))`. -/
def orderId (chainId : ℕ) (o : AsyncOrder) : ℕ :=
  M.keccak (.tuple [chainId, poolId M o.key, o.owner, boolWord o.zeroForOne, o.salt])

/-! ## Injectivity of the building blocks -/

theorem keccak_str_inj {s s' : String} (h : M.keccak (.str s) = M.keccak (.str s')) : s = s' := by
  have := M.injective h; simpa using this

theorem keccak_tuple_inj {ws ws' : List ℕ} (h : M.keccak (.tuple ws) = M.keccak (.tuple ws')) : ws = ws' := by
  have := M.injective h; simpa using this

theorem keccak_typed_inj {d s d' s' : ℕ} (h : M.keccak (.typed d s) = M.keccak (.typed d' s')) :
    d = d' ∧ s = s' := by
  have := M.injective h; simpa using this

theorem keccak_str_ne_tuple (s : String) (ws : List ℕ) : M.keccak (.str s) ≠ M.keccak (.tuple ws) :=
  fun h => by have := M.injective h; simp at this

theorem poolId_inj {k k' : PoolKey} (h : poolId M k = poolId M k') : k = k' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨h0, h1, h2, h3, h4⟩ := this
  cases k; cases k'; simp_all

theorem hashPoolKey_inj {k k' : PoolKey} (h : hashPoolKey M k = hashPoolKey M k') : k = k' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h0, h1, h2, h3, h4⟩ := this
  cases k; cases k'; simp_all

/-- `tokens` determines the direction once the pool's two currencies differ (Uniswap v4 orders
    `currency0 < currency1`, so they always do). -/
theorem tokens_inj {o o' : AsyncOrder} (hk : o.key = o'.key) (hne : o.key.currency0 ≠ o.key.currency1)
    (h : o.tokens = o'.tokens) : o.zeroForOne = o'.zeroForOne := by
  unfold AsyncOrder.tokens at h
  rw [← hk] at h
  cases hz : o.zeroForOne <;> cases hz' : o'.zeroForOne <;> simp_all

/-! ## Witness binding -/

/-- **Permit2 witness binding.** Two orders with the same witness hash agree on everything the
    maker signed: maker, pool, amounts, bid, and (for a legitimate pool) direction. -/
theorem hashOrder_inj {o o' : AsyncOrder} (h : hashOrder M o = hashOrder M o') :
    o.key = o'.key ∧ o.owner = o'.owner ∧ o.amountIn = o'.amountIn ∧ o.amountOutMin = o'.amountOutMin ∧
    o.priorityFee = o'.priorityFee ∧ o.tokens = o'.tokens ∧
    (o.key.currency0 ≠ o.key.currency1 → o.zeroForOne = o'.zeroForOne) := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := this
  have hk := hashPoolKey_inj M h7
  refine ⟨hk, h1, h4, h5, h6, Prod.ext h2 h3, fun hne => tokens_inj hk hne (Prod.ext h2 h3)⟩

/-- **`swapWithSig` binding.** The Permit2 message the maker signs fixes the token pulled (the
    order's input token), the amount (`amountIn`), the spender (the Router), nonce, deadline, and
    the whole order witness. A relayer cannot substitute any of them. -/
theorem routerPermit_inj {router router' : Address} {o o' : AsyncOrder} {n d n' d' : ℕ}
    (h : routerPermitStructHash M router o n d = routerPermitStructHash M router' o' n' d') :
    router = router' ∧ n = n' ∧ d = d' ∧ o.tokens.1 = o'.tokens.1 ∧ o.amountIn = o'.amountIn ∧
    hashOrder M o = hashOrder M o' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := this
  have := keccak_tuple_inj M h1
  simp only [List.cons.injEq, and_true] at this
  exact ⟨h2, h3, h4, this.2.1, this.2.2, h5⟩

/-- **`setExecutorWithSig` binding.** -/
theorem hashSetExecutor_inj {k k' : PoolKey} {m e m' e' : Address} {a a' : Bool} {n d n' d' : ℕ}
    (h : hashSetExecutor M k m e a n d = hashSetExecutor M k' m' e' a' n' d') :
    k = k' ∧ m = m' ∧ e = e' ∧ a = a' ∧ n = n' ∧ d = d' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := this
  exact ⟨hashPoolKey_inj M h4, h1, h2, boolWord_inj h3, h5, h6⟩

/-- **`updatePriceWithSig` binding.** The maker signs the order id, the stored size and the new
    minimum output. -/
theorem hashUpdatePrice_inj {o o' : AsyncOrder} {id a m n d id' a' m' n' d' : ℕ}
    (h : hashUpdatePrice M o id a m n d = hashUpdatePrice M o' id' a' m' n' d') :
    o.owner = o'.owner ∧ o.tokens = o'.tokens ∧ a = a' ∧ m = m' ∧ id = id' ∧ n = n' ∧ d = d' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := this
  exact ⟨h1, Prod.ext h2 h3, h4, h5, h6, h7, h8⟩

/-- **`cancelWithSig` binding.** -/
theorem hashCancel_inj {o o' : AsyncOrder} {id a n d id' a' n' d' : ℕ}
    (h : hashCancel M o id a n d = hashCancel M o' id' a' n' d') :
    o.owner = o'.owner ∧ o.tokens = o'.tokens ∧ a = a' ∧ id = id' ∧ n = n' ∧ d = d' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := this
  exact ⟨h1, Prod.ext h2 h3, h4, h5, h6, h7⟩

/-- **Order id.** Two orders with the same id are on the same chain and pool, by the same maker,
    in the same direction, with the same salt. Amounts are not part of the id, which is why
    signed cancels carry a nonce. -/
theorem orderId_inj {c c' : ℕ} {o o' : AsyncOrder} (h : orderId M c o = orderId M c' o') :
    c = c' ∧ o.key = o'.key ∧ o.owner = o'.owner ∧ o.zeroForOne = o'.zeroForOne ∧ o.salt = o'.salt := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨h0, h1, h2, h3, h4⟩ := this
  exact ⟨h0, poolId_inj M h1, h2, boolWord_inj h3, h4⟩

/-! ## Type separation: a struct hash of one type never equals one of another -/

theorem typehash_ne {s s' : String} (hs : s ≠ s') : M.keccak (.str s) ≠ M.keccak (.str s') :=
  fun h => hs (keccak_str_inj M h)

/-- Struct hashes with different leading typehashes differ. -/
theorem tuple_ne_of_head {t t' : ℕ} (ht : t ≠ t') (ws ws' : List ℕ) :
    M.keccak (.tuple (t :: ws)) ≠ M.keccak (.tuple (t' :: ws')) :=
  fun h => ht (List.cons.inj (keccak_tuple_inj M h)).1

theorem hashOrder_ne_hashSetExecutor (o : AsyncOrder) (k : PoolKey) (m e : Address) (a : Bool) (n d : ℕ) :
    hashOrder M o ≠ hashSetExecutor M k m e a n d :=
  tuple_ne_of_head M (typehash_ne M (by simp [ASYNC_ORDER_TYPE, SET_EXECUTOR_TYPE, POOL_KEY_TYPE])) _ _
theorem hashOrder_ne_hashUpdatePrice (o o' : AsyncOrder) (id a m n d : ℕ) :
    hashOrder M o ≠ hashUpdatePrice M o' id a m n d :=
  tuple_ne_of_head M (typehash_ne M (by simp [ASYNC_ORDER_TYPE, UPDATE_PRICE_TYPE, POOL_KEY_TYPE])) _ _
theorem hashOrder_ne_hashCancel (o o' : AsyncOrder) (id a n d : ℕ) :
    hashOrder M o ≠ hashCancel M o' id a n d :=
  tuple_ne_of_head M (typehash_ne M (by simp [ASYNC_ORDER_TYPE, CANCEL_ORDER_TYPE, POOL_KEY_TYPE])) _ _
theorem hashSetExecutor_ne_hashUpdatePrice (k : PoolKey) (m e : Address) (a : Bool) (n d : ℕ)
    (o : AsyncOrder) (id a' m' n' d' : ℕ) :
    hashSetExecutor M k m e a n d ≠ hashUpdatePrice M o id a' m' n' d' :=
  tuple_ne_of_head M (typehash_ne M (by simp [SET_EXECUTOR_TYPE, UPDATE_PRICE_TYPE, POOL_KEY_TYPE])) _ _
theorem hashSetExecutor_ne_hashCancel (k : PoolKey) (m e : Address) (a : Bool) (n d : ℕ)
    (o : AsyncOrder) (id a' n' d' : ℕ) :
    hashSetExecutor M k m e a n d ≠ hashCancel M o id a' n' d' :=
  tuple_ne_of_head M (typehash_ne M (by simp [SET_EXECUTOR_TYPE, CANCEL_ORDER_TYPE, POOL_KEY_TYPE])) _ _
theorem hashUpdatePrice_ne_hashCancel (o : AsyncOrder) (id a m n d : ℕ) (o' : AsyncOrder) (id' a' n' d' : ℕ) :
    hashUpdatePrice M o id a m n d ≠ hashCancel M o' id' a' n' d' :=
  tuple_ne_of_head M (typehash_ne M (by simp [UPDATE_PRICE_TYPE, CANCEL_ORDER_TYPE])) _ _
/-- A struct hash is never a pool key hash or a Permit2 message hash either. -/
theorem hashOrder_ne_hashPoolKey (o : AsyncOrder) (k : PoolKey) : hashOrder M o ≠ hashPoolKey M k :=
  tuple_ne_of_head M (typehash_ne M (by simp [ASYNC_ORDER_TYPE, POOL_KEY_TYPE])) _ _
theorem hashOrder_ne_permitWitness (o : AsyncOrder) (t a s n d w : ℕ) :
    hashOrder M o ≠ permitWitnessStructHash M t a s n d w :=
  tuple_ne_of_head M (typehash_ne M (by simp [ASYNC_ORDER_TYPE, POOL_KEY_TYPE, PERMIT_WITNESS_TRANSFER_FROM_TYPE, PERMIT2_WITNESS_TYPE, TOKEN_PERMISSIONS_TYPE])) _ _

/-! ## Domain separation -/

theorem domainSeparator_inj {d d' : Domain} (h : domainSeparator M d = domainSeparator M d') : d = d' := by
  have := keccak_tuple_inj M h
  simp only [List.cons.injEq, and_true] at this
  obtain ⟨-, h1, h2, h3, h4⟩ := this
  obtain ⟨n, v, c, a⟩ := d
  obtain ⟨n', v', c', a'⟩ := d'
  simp only at h1 h2 h3 h4
  rw [keccak_str_inj M h1, keccak_str_inj M h2, h3, h4]

/-- **Digest binding.** Equal digests mean the same domain (name, version, chain, contract) and the
    same struct hash: a signature for the hook's domain is never valid for the Router's or
    Permit2's, and never for another chain. -/
theorem digest_inj {d d' : Domain} {s s' : ℕ} (h : digest M d s = digest M d' s') : d = d' ∧ s = s' := by
  obtain ⟨h1, h2⟩ := keccak_typed_inj M h
  exact ⟨domainSeparator_inj M h1, h2⟩

theorem digest_ne_of_contract {d d' : Domain} (hc : d.verifyingContract ≠ d'.verifyingContract) (s s' : ℕ) :
    digest M d s ≠ digest M d' s' :=
  fun h => hc (congrArg Domain.verifyingContract (digest_inj M h).1)

theorem digest_ne_of_chain {d d' : Domain} (hc : d.chainId ≠ d'.chainId) (s s' : ℕ) :
    digest M d s ≠ digest M d' s' :=
  fun h => hc (congrArg Domain.chainId (digest_inj M h).1)

end Hashing
end AsyncSwap
