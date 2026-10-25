import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
open StatMech StatMech.FrontierD


/--
[fkRectDualPullbackIndexSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPullbackIndexSet_card_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex} :
-- imply
  (fkRectDualPullbackIndexSet R I).card = I.card := by
-- proof
  apply StatMech.FrontierD.fkRectDualPullbackIndexSet_card R I

/--
[fkRectDualPreimage_indexedPatternEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPreimage_indexedPatternEvent_eq_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration} :
-- imply
  fkRectDualPreimageEvent R (fkRectIndexedPatternEvent R I eta) = fkRectIndexedPatternEvent R (fkRectDualPullbackIndexSet R I) (fkRectDualPullbackConfiguration R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectDualPreimage_indexedPatternEvent_eq R I eta

/--
[fkRectDualPullbackHorizontalCutEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPullbackHorizontalCutEdges_card_eq
  {R : FKRectTorus} :
-- imply
  (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)).card = 2 * R.width := by
-- proof
  apply StatMech.FrontierD.fkRectDualPullbackHorizontalCutEdges_card R

/--
[fkRectDualPullbackIndexSet_horizontalCutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPullbackIndexSet_horizontalCutEdges_eq
  {R : FKRectTorus} :
-- imply
  fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R) = fkRectHorizontalCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectDualPullbackIndexSet_horizontalCutEdges R

/--
[fkRectDualPreimage_noLeftStripCrossing_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPreimage_noLeftStripCrossing_isIncreasing_eq
  {R : FKRectTorus}
  {leftRight : Nat} :
-- imply
  IsIncreasing (fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R leftRight)) := by
-- proof
  apply StatMech.FrontierD.fkRectDualPreimage_noLeftStripCrossing_isIncreasing R leftRight

/--
[fkRectDualPullbackSourceLeftBarrier_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectDualPullbackSourceLeftBarrier_eq_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex} :
-- imply
  fkRectDualPullbackSourceLeftBarrier R leftRight gap = fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R leftRight) ∩ fkRectIndexedPatternEvent R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R gap)) := by
-- proof
  apply StatMech.FrontierD.fkRectDualPullbackSourceLeftBarrier_eq R leftRight gap

/--
[fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierPattern.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (hforce : ∀ omega ∈ A, fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R gap)) omega ∈ fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R leftRight)) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * fkRectCriticalEventMass R q A <= fkRectCriticalEventMass R q (fkRectDualPullbackSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_width_mul_auxiliary_le_dualPullbackSource R leftRight hq gap A hforce


-- created on 2026-10-23
