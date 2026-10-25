import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
open StatMech StatMech.Universality


/--
[hbw_widthlist_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean)
-/
@[path]
private lemma hbw_widthlist_nodup_eq
  {bs : List HexBridge}
-- given
  (h : StrictDecreasingWidths bs) :
-- imply
  (bs.map HexBridge.width).Nodup := by
-- proof
  apply StatMech.Universality.hbw_widthlist_nodup bs h

/--
[hbw_prod_eq_finsetProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean)
-/
@[path]
private lemma hbw_prod_eq_finsetProd_eq
  {bs : List HexBridge}
  {υ : ℕ → ℝ}
-- given
  (h : StrictDecreasingWidths bs) :
-- imply
  (bs.map (fun b => υ b.width)).prod = ∏ T ∈ hbw_widthFinset bs, υ T := by
-- proof
  apply StatMech.Universality.hbw_prod_eq_finsetProd bs h υ

/--
[hbw_bridgeProd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean)
-/
@[path]
private lemma hbw_bridgeProd_le_eq
  {bs : List HexBridge}
  {υ wt : ℕ → ℝ}
-- given
  (h : StrictDecreasingWidths bs)
  (hdom : ∀ b ∈ bs, wt b.width ≤ υ b.width)
  (hwtnn : ∀ b ∈ bs, 0 ≤ wt b.width) :
-- imply
  (bs.map (fun b => wt b.width)).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
-- proof
  apply StatMech.Universality.hbw_bridgeProd_le bs h υ wt hdom hwtnn

/--
[hbw_weightBound_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean)
-/
@[path]
private lemma hbw_weightBound_factor_eq
  {x g : ℝ}
  {lower upper : List HexBridge}
  {υ wt : ℕ → ℝ}
-- given
  (hx : 0 < x)
  (hlo : StrictDecreasingWidths lower)
  (hup : StrictDecreasingWidths upper)
  (hdomLo : ∀ b ∈ lower, wt b.width ≤ υ b.width)
  (hdomUp : ∀ b ∈ upper, wt b.width ≤ υ b.width)
  (hwtnn : ∀ T, 0 ≤ wt T)
  (htwo : g * x ^ 2 = (lower.map (fun b => wt b.width)).prod * (upper.map (fun b => wt b.width)).prod) :
-- imply
  g ≤ (x ^ 2)⁻¹ * ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
-- proof
  apply StatMech.Universality.hbw_weightBound_factor x g hx lower upper hlo hup υ wt hdomLo hdomUp hwtnn htwo

/--
[hexZ_conv_domination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeWeight.lean)
-/
@[path]
private lemma hexZ_conv_domination_eq
  {c : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 < x)
  (hlt : x < hexChiE)
  (hc : ∀ n, 0 ≤ c n)
  (C : ∀ T, HexColumn T hexChiE)
  (H : ∀ N, HexHWDataRecon c (fun T => (C T).colSum x) x N) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_conv_domination c x hx hlt hc C H


-- created on 2026-10-23
