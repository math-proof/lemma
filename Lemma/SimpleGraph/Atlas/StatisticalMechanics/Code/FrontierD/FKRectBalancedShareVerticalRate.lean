import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare_eq
  {r k m : Nat}
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily r k m) q = sixVertexBalancedTraceShare (fkRectFixedChargeVerticalFamily r k m).medialTorus.width (fkRectFixedChargeVerticalFamily r k m).medialTorus.height (fkQgt4SixVertexWeight q) := by
-- proof
  apply StatMech.FrontierD.fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare r k m hq

/--
[fkRectBalancedSectorShare_vertical_negLog_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_vertical_negLog_tendsto_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds (Real.log (sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) - Real.log (sixVertexLambdaAlongFour (fkQgt4SixVertexWeight q) 0 (k + 1)))) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_vertical_negLog_tendsto hq k

/--
[fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hcentral : sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q) = sixVertexLambdaAlongFour (fkQgt4SixVertexWeight q) 0 (k + 1)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_central_max hq k hcentral

/--
[fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalf_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hdom : SixVertexStrictLowerHalfDominance (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalf hq k hdom

/--
[fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hdom : SixVertexStrictLowerHalfDominanceAboveOne (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorShare (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorShare_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne hq k hdom

/--
[fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hcentral : sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q) = sixVertexLambdaAlongFour (fkQgt4SixVertexWeight q) 0 (k + 1))
  (hall : Tendsto (fun m => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero hq k hcentral hall

/--
[fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalf_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hdom : SixVertexStrictLowerHalfDominance (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q))
  (hall : Tendsto (fun m => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalf hq k hdom hall

/--
[fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareVerticalRate.lean)
-/
@[path]
private lemma fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne_eq
  {q : Real}
  {k : Nat}
-- given
  (hq : 4 < q)
  (hdom : SixVertexStrictLowerHalfDominanceAboveOne (sixVertexFourWidth 0 (k + 1)) (fkQgt4SixVertexWeight q))
  (hall : Tendsto (fun m => -Real.log (fkRectAllSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun m => -Real.log (fkRectBalancedSectorNormalization (fkRectFixedChargeVerticalFamily 0 k m) q) / (fkRectFixedChargeVerticalFamily 0 k m).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedSectorNormalization_vertical_negLog_tendsto_zero_of_strictLowerHalfAboveOne hq k hdom hall


-- created on 2026-10-23
