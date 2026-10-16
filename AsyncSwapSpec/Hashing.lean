import Mathlib.Data.Nat.Notation
import Mathlib.Logic.Function.Basic

/-!
# EIP-712 struct hashing for the signed maker payloads

Start of roadmap item 6 (decision 4, hashing model). The two maker payloads that carry a
signature, `cancel` and `permitOrder` (`SigPayload` in `AsyncSwapProtocol/V2/Model.lean`), are
hashed the EIP-712 way:

* `typeHash = keccak(typeString)`,
* `structHash = keccak(abi.encode(typeHash, field₁, …, fieldₙ))` in the Solidity field order,
* `digest = keccak(0x1901 ‖ domainSeparator ‖ structHash)`.

keccak256 stays abstract: every definition takes it as an argument `keccak : List ℕ → ℕ` over
the encoded word list, and the theorems assume `Function.Injective keccak` (the standing
assumption in `README.md`). No axiom is added. `abi.encode` of fixed-size fields is one 32-byte
word per field, so a list of words is the exact preimage; `bool` is encoded as `0` / `1`; the
type string is the list of its character codes.

The payload fields follow `SigPayload`: `cancel` flattens its `OrderKey` into
`(owner, zeroForOne, salt)`. This file cannot import `AsyncSwapProtocol` (that library imports
this one), so the payload type is restated here; wiring `sigOk` to `digest` is a later issue,
as is Permit2 witness binding.
-/

namespace AsyncSwap.Hashing

/-- The two signed maker payloads, fields in the order they are hashed. -/
inductive Payload
  | cancel (owner : ℕ) (zeroForOne : Bool) (salt storedAmountIn nonce deadline : ℕ)
  | permitOrder (owner : ℕ) (zeroForOne : Bool) (amountIn amountOutMin nonce deadline : ℕ)
  deriving DecidableEq, Repr

/-- EIP-712 type string of `cancel`. -/
def cancelType : String :=
  "Cancel(address owner,bool zeroForOne,uint256 salt,uint256 storedAmountIn,uint256 nonce,uint256 deadline)"

/-- EIP-712 type string of `permitOrder`. -/
def permitOrderType : String :=
  "PermitOrder(address owner,bool zeroForOne,uint256 amountIn,uint256 amountOutMin,uint256 nonce,uint256 deadline)"

/-- A string as the word list keccak sees: its character codes. -/
def encodeString (s : String) : List ℕ := s.toList.map Char.toNat

section
variable (keccak : List ℕ → ℕ)

def cancelTypeHash : ℕ := keccak (encodeString cancelType)

def permitOrderTypeHash : ℕ := keccak (encodeString permitOrderType)

/-- `keccak(abi.encode(TYPEHASH, fields…))`. -/
def structHash : Payload → ℕ
  | .cancel owner z salt amt nonce deadline =>
      keccak [cancelTypeHash keccak, owner, z.toNat, salt, amt, nonce, deadline]
  | .permitOrder owner z amtIn amtOutMin nonce deadline =>
      keccak [permitOrderTypeHash keccak, owner, z.toNat, amtIn, amtOutMin, nonce, deadline]

/-- `keccak(0x1901 ‖ domainSeparator ‖ structHash)`. -/
def digest (domainSeparator : ℕ) (p : Payload) : ℕ :=
  keccak [0x1901, domainSeparator, structHash keccak p]

end

variable {keccak : List ℕ → ℕ}

theorem cancelTypeHash_ne_permitOrderTypeHash (hk : Function.Injective keccak) :
    cancelTypeHash keccak ≠ permitOrderTypeHash keccak := by
  intro h
  have h' := hk h
  simp only [encodeString, cancelType, permitOrderType] at h'
  exact absurd (congrArg List.head? h') (by decide)

private theorem bool_toNat_inj {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Equal struct hashes mean the same payload: same kind and equal fields. -/
theorem structHash_injective (hk : Function.Injective keccak) :
    Function.Injective (structHash keccak) := by
  intro p q h
  cases p <;> cases q <;> simp only [structHash] at h <;> have h' := hk h <;>
    simp only [List.cons.injEq, and_true] at h'
  · obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h'
    rw [bool_toNat_inj h2, h1, h3, h4, h5, h6]
  · exact absurd h'.1 (cancelTypeHash_ne_permitOrderTypeHash hk)
  · exact absurd h'.1.symm (cancelTypeHash_ne_permitOrderTypeHash hk)
  · obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := h'
    rw [bool_toNat_inj h2, h1, h3, h4, h5, h6]

/-- Under one domain separator, equal digests mean the same payload. -/
theorem digest_injective (hk : Function.Injective keccak) (domainSeparator : ℕ) :
    Function.Injective (digest keccak domainSeparator) := by
  intro p q h
  have h' := hk h
  simp only [List.cons.injEq, true_and, and_true] at h'
  exact structHash_injective hk h'

/-- A cancel signature can never be replayed as an order permit, under any two domains. -/
theorem digest_cancel_ne_permitOrder (hk : Function.Injective keccak) (ds ds' : ℕ)
    (owner : ℕ) (z : Bool) (salt storedAmountIn nonce deadline : ℕ)
    (owner' : ℕ) (z' : Bool) (amountIn amountOutMin nonce' deadline' : ℕ) :
    digest keccak ds (.cancel owner z salt storedAmountIn nonce deadline) ≠
      digest keccak ds' (.permitOrder owner' z' amountIn amountOutMin nonce' deadline') := by
  intro h
  have h' := hk h
  simp only [List.cons.injEq, true_and, and_true] at h'
  exact absurd (structHash_injective hk h'.2) (by simp)

end AsyncSwap.Hashing
