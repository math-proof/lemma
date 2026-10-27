import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part4
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexOddWallisReferenceProduct_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma tendsto_sixVertexOddWallisReferenceProduct_bridge_eq
  {s : Nat} :
-- imply
  Tendsto (fun k => (sixVertexFourWidth (2 * s + 1) k : Real) * sixVertexOddWallisHalfProduct (s + k + 1) ^ 2) atTop (nhds (4 / Real.pi)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexOddWallisReferenceProduct_bridge s

/--
[sixVertexCanonicalOddActualHalfProduct_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma sixVertexCanonicalOddActualHalfProduct_pos_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexCanonicalOddActualHalfProduct hc s k := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddActualHalfProduct_pos hc s k

/--
[sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (hfixed : SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k)) :
-- imply
  sixVertexCanonicalOddZeroModeWallisCorrection hc s k = Real.log ((sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth (2 * s + 1) k) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexOddCentralIndex (s + k + 1)) / 2) * sixVertexCanonicalOddActualHalfProduct hc s k ^ 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product hc s k hfixed

/--
[log_sixVertexCanonicalOddWallisProductRatio_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma log_sixVertexCanonicalOddWallisProductRatio_sq_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Real.log (sixVertexCanonicalOddWallisProductRatio hc s k ^ 2) = sixVertexCanonicalOddSmoothWallisLog hc s k - 2 * ( let N := sixVertexFourWidth (2 * s + 1) k let n := (2 * s + 1 + k + 1) + (2 * s + 1 + k + 1) let p := sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k) ∑ j : Fin (s + k + 1), (Real.log (sixVertexBetheCountingFunction c N n p (sixVertexCanonicalOddMidpointHalfRoot hc s k j)) - Real.log (((j : Real) + 1) / N))) := by
-- proof
  apply StatMech.FrontierD.log_sixVertexCanonicalOddWallisProductRatio_sq hc s k

/--
[sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hsmooth : SixVertexCanonicalOddSmoothWallisLimit hc s) :
-- imply
  SixVertexCanonicalOddGeneralizedWallisComparison hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddGeneralizedWallisComparison_of_smooth hc s hsmooth

/--
[tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
-- imply
  Tendsto (sixVertexCanonicalOddWallisProductArgument hc s) atTop (nhds (Real.cosh (sixVertexAntiferroelectricLambda c))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison hc s hcomparison

/--
[sixVertexCanonicalOddZeroModeWallisLimit_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma sixVertexCanonicalOddZeroModeWallisLimit_of_comparison_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
-- imply
  SixVertexCanonicalOddZeroModeWallisLimit hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddZeroModeWallisLimit_of_comparison hc s hcomparison

/--
[sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
-- imply
  SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc (2 * s + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison hc s hcomparison


-- created on 2026-10-23
