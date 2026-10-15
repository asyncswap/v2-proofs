import AsyncSwapSpec.Order

/-!
# Order-to-order matching amounts

Models `AsyncMatching._matchAmounts` (src/libraries/AsyncMatching.sol).  The resting
(earlier-sequence) side's price is used to size the trade; the incoming side's
limit is then checked.  We prove that whenever the function returns non-zero amounts:

* neither escrow is overspent (`asset ≤ sell.amountIn`, `quote ≤ buy.amountIn`);
* the **seller** receives at least its pro-rata minimum: `asset · sell.min ≤ quote · sell.in`;
* the **buyer** receives at least its pro-rata minimum: `quote · buy.min ≤ asset · buy.in`;
* consequently the two limit prices cross (`buy.min · sell.min ≤ buy.in · sell.in`).

A *buy* order spends numeraire (`amountIn` = quote) for asset (`amountOutMin`);
a *sell* order spends asset for numeraire.
-/

namespace AsyncSwap

structure MatchAmounts where
  assetAmount : ℕ
  quoteAmount : ℕ
  deriving Repr, DecidableEq

/-- `_matchAmounts(sell, buy, restingBuy)`, line for line. -/
def matchAmounts (sell buy : Order) (restingBuy : Bool) : MatchAmounts :=
  if restingBuy then
    -- quote = sell.amountIn * buy.amountIn / buy.amountOutMin, capped at buy.amountIn
    let quote := min (mulDiv sell.amountIn buy.amountIn buy.amountOutMin) buy.amountIn
    if quote = 0 then ⟨0, 0⟩
    else
      let asset := mulDivCeil quote buy.amountOutMin buy.amountIn
      if sell.amountIn < asset then ⟨0, 0⟩
      else
        let sellerMinimum := mulDivCeil asset sell.amountOutMin sell.amountIn
        if quote < sellerMinimum then ⟨0, 0⟩ else ⟨asset, quote⟩
  else
    -- asset = buy.amountIn * sell.amountIn / sell.amountOutMin, capped at sell.amountIn
    let asset := min (mulDiv buy.amountIn sell.amountIn sell.amountOutMin) sell.amountIn
    if asset = 0 then ⟨0, 0⟩
    else
      let quote := mulDivCeil asset sell.amountOutMin sell.amountIn
      if buy.amountIn < quote then ⟨0, 0⟩
      else
        let buyerMinimum := mulDivCeil quote buy.amountOutMin buy.amountIn
        if asset < buyerMinimum then ⟨0, 0⟩ else ⟨asset, quote⟩

/-- Everything `_matchPair` relies on after a non-zero `_matchAmounts` result. -/
structure MatchSound (sell buy : Order) (m : MatchAmounts) : Prop where
  asset_le_sell_escrow : m.assetAmount ≤ sell.amountIn
  quote_le_buy_escrow  : m.quoteAmount ≤ buy.amountIn
  seller_limit : m.assetAmount * sell.amountOutMin ≤ m.quoteAmount * sell.amountIn
  buyer_limit  : m.quoteAmount * buy.amountOutMin ≤ m.assetAmount * buy.amountIn

/-- **Main matching theorem.**  A non-zero match honours both limit prices and both escrows. -/
theorem matchAmounts_sound (sell buy : Order) (rb : Bool)
    (hs : 0 < sell.amountIn) (hb : 0 < buy.amountIn)
    (m : MatchAmounts) (hm : matchAmounts sell buy rb = m)
    (ha : m.assetAmount ≠ 0) (hq : m.quoteAmount ≠ 0) :
    MatchSound sell buy m := by
  cases rb <;> simp only [matchAmounts, Bool.false_eq_true, ↓reduceIte] at hm
  · -- resting side is the seller: `asset` is sized from the seller's price
    split_ifs at hm with h1 h2 h3
    all_goals (subst hm; try simp at ha)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · exact min_le_right _ _
    · omega
    · exact le_mulDivCeil_mul hs
    · calc _ ≤ _ := le_mulDivCeil_mul hb
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · -- resting side is the buyer: `quote` is sized from the buyer's price
    split_ifs at hm with h1 h2 h3
    all_goals (subst hm; try simp at ha)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only
    · omega
    · exact min_le_right _ _
    · calc _ ≤ _ := le_mulDivCeil_mul hs
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · exact le_mulDivCeil_mul hb

/-- A successful match implies the limit prices cross:
    `bid = buy.in / buy.min ≥ ask = sell.min / sell.in`.
    The radix-tree price check in `matchIncoming` / `matchBook` is therefore a
    *filter*, not the safety mechanism — `_matchAmounts` is safe on its own. -/
theorem matchAmounts_cross (sell buy : Order) (m : MatchAmounts)
    (hsound : MatchSound sell buy m) (ha : 0 < m.assetAmount) (hq : 0 < m.quoteAmount) :
    buy.amountOutMin * sell.amountOutMin ≤ buy.amountIn * sell.amountIn := by
  have h := Nat.mul_le_mul hsound.seller_limit hsound.buyer_limit
  have h' : (m.assetAmount * m.quoteAmount) * (buy.amountOutMin * sell.amountOutMin)
            ≤ (m.assetAmount * m.quoteAmount) * (buy.amountIn * sell.amountIn) := by
    calc (m.assetAmount * m.quoteAmount) * (buy.amountOutMin * sell.amountOutMin)
        = m.assetAmount * sell.amountOutMin * (m.quoteAmount * buy.amountOutMin) := by ring
      _ ≤ m.quoteAmount * sell.amountIn * (m.assetAmount * buy.amountIn) := h
      _ = (m.assetAmount * m.quoteAmount) * (buy.amountIn * sell.amountIn) := by ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.mul_pos ha hq)

/-- Rounding favours the resting order by at most one unit of its output: when the buyer
    rests, `asset` is the *least* amount satisfying the buyer's limit. -/
theorem matchAmounts_restingBuy_tight (sell buy : Order)
    (hb : 0 < buy.amountIn) (m : MatchAmounts) (hm : matchAmounts sell buy true = m)
    (ha : m.assetAmount ≠ 0) :
    m.assetAmount * buy.amountIn < m.quoteAmount * buy.amountOutMin + buy.amountIn := by
  simp only [matchAmounts, ↓reduceIte] at hm
  split_ifs at hm with h1 h2 h3
  all_goals (subst hm; try simp at ha)
  dsimp only
  exact mulDivCeil_mul_lt hb

/-- Symmetric statement when the seller rests: `quote` is the least amount satisfying the
    seller's limit. -/
theorem matchAmounts_restingSell_tight (sell buy : Order)
    (hs : 0 < sell.amountIn) (m : MatchAmounts) (hm : matchAmounts sell buy false = m)
    (ha : m.assetAmount ≠ 0) :
    m.quoteAmount * sell.amountIn < m.assetAmount * sell.amountOutMin + sell.amountIn := by
  simp only [matchAmounts, Bool.false_eq_true, ↓reduceIte] at hm
  split_ifs at hm with h1 h2 h3
  all_goals (subst hm; try simp at ha)
  dsimp only
  exact mulDivCeil_mul_lt hs

end AsyncSwap
