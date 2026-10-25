import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeparatedWindingNoNet
open StatMech StatMech.FrontierD


/--
[fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeparatedWindingNoNet.lean)
-/
@[path]
private lemma fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne_eq
  {R : FKRectTorus}
  {leftRight : Nat}
-- given
  (hleft : leftRight + 1 < R.width) :
-- imply
  fkRectSeparatedVerticalWindingEvent R leftRight ⊆ fkRectVerticalRankOneEvent R := by
-- proof
  apply StatMech.FrontierD.fkRectSeparatedVerticalWindingEvent_subset_verticalRankOne R leftRight hleft

/--
[fkRectCriticalSeparatedVerticalWindingMass_le_verticalRankOneMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeparatedWindingNoNet.lean)
-/
@[path]
private lemma fkRectCriticalSeparatedVerticalWindingMass_le_verticalRankOneMass_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {q : Real}
-- given
  (hleft : leftRight + 1 < R.width)
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectSeparatedVerticalWindingEvent R leftRight) ≤ fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalSeparatedVerticalWindingMass_le_verticalRankOneMass R leftRight hleft hq

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_verticalRankOneMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSeparatedWindingNoNet.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_verticalRankOneMass_eq
  {R : FKRectTorus}
  {leftRight cut : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 ≤ q)
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (hx : cut ≤ x.val)
  (hchosen : fkRectVerticalSeamEdgeAt R x ≠ gap)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_verticalRankOneMass R leftRight cut hsep hleft hq hgap x hx hchosen t hpair


-- created on 2026-10-23
