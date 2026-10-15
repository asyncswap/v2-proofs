import AsyncSwapSpec.Arith

/-!
# Orders

`AsyncFiller.OrderInfo` (src/libraries/AsyncFiller.sol), restricted to the fields that
carry value.  Book-position fields (`previous`, `next`, `sequence`, `priorityKey`) and
the radix price index are abstracted away: see README.
-/

namespace AsyncSwap

abbrev Address := ℕ
abbrev OrderId := ℕ

structure Order where
  owner : Address
  /-- Remaining escrowed input. `0` means "no such order" exactly as in storage. -/
  amountIn : ℕ
  /-- Remaining minimum output the maker still has to receive. -/
  amountOutMin : ℕ
  isBuy : Bool
  /-- `true` ⇒ input is currency0, output is currency1. -/
  zeroForOne : Bool
  /-- Remaining non-refundable priority bid (numeraire units). -/
  priorityFee : ℕ
  priorityFeeEscrowed : Bool
  deriving Repr, DecidableEq

namespace Order

/-- Storage well-formedness for an *open* order.  `_priceKey` divides by `amountOutMin`
    for buys and by `amountIn` for sells, so both must be positive. -/
def wf (o : Order) : Prop := 0 < o.amountIn ∧ 0 < o.amountOutMin

def closed (o : Order) : Prop := o.amountIn = 0 ∨ o.amountOutMin = 0

/-- Input currency escrow in currency0. -/
def escrow0 (o : Order) : ℕ := if o.zeroForOne then o.amountIn else 0

/-- Escrow in currency1 (the numeraire): input if selling currency1, plus the escrowed bid. -/
def escrow1 (o : Order) : ℕ :=
  (if o.zeroForOne then 0 else o.amountIn) + (if o.priorityFeeEscrowed then o.priorityFee else 0)

end Order

/-- `AsyncFiller.PRICE_SCALE`. -/
def priceScale : ℕ := 10 ^ 18

/-- Unclamped WAD price: `amountIn / amountOut` for bids, `amountOut / amountIn` for asks,
    so that a higher key is always a *better* price for the counterparty. -/
def rawPrice (isBuy : Bool) (amountIn amountOut : ℕ) : ℕ :=
  if isBuy then mulDiv amountIn priceScale amountOut else mulDiv amountOut priceScale amountIn

/-- `AsyncFiller._priceKey`: WAD-scaled price, clamped into `[1, 2^128 − 1]` so it is a valid
    radix-tree key. -/
def priceKey (isBuy : Bool) (amountIn amountOut : ℕ) : ℕ :=
  if rawPrice isBuy amountIn amountOut = 0 then 1
  else if rawPrice isBuy amountIn amountOut > 2 ^ 128 - 1 then 2 ^ 128 - 1
  else rawPrice isBuy amountIn amountOut

theorem priceKey_pos (isBuy : Bool) (a b : ℕ) : 0 < priceKey isBuy a b := by
  unfold priceKey
  generalize rawPrice isBuy a b = p
  split_ifs <;> omega

theorem priceKey_lt (isBuy : Bool) (a b : ℕ) : priceKey isBuy a b < 2 ^ 128 := by
  unfold priceKey
  generalize rawPrice isBuy a b = p
  split_ifs <;> omega

/-- `AsyncFiller.MIN_PRIORITY_FEE` — $0.10 in six-decimal USDC. -/
def minPriorityFee : ℕ := 100000
/-- `AsyncFiller.MAX_PRIORITY_FEE` — `type(uint64).max`. -/
def maxPriorityFee : ℕ := 2 ^ 64 - 1

end AsyncSwap
