import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
open StatMech StatMech.FrontierD


/--
[fkRectVerticalRankOneEvent_subset_windingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRankOneWindingTail.lean)
-/
@[path]
private lemma fkRectVerticalRankOneEvent_subset_windingTail_eq
  {R : FKRectTorus} :
-- imply
  fkRectVerticalRankOneEvent R ⊆ {omega | 1 ≤ fkRectUnorientedVerticalWindingNumber R omega} := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalRankOneEvent_subset_windingTail R

/--
[fkRectCriticalVerticalRankOneMass_le_windingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRankOneWindingTail.lean)
-/
@[path]
private lemma fkRectCriticalVerticalRankOneMass_le_windingTail_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectVerticalRankOneEvent R) ≤ fkRectCriticalWindingTailMass R q 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalVerticalRankOneMass_le_windingTail R hq

/--
[fkRectAugmentedSource_barrierConnectionProduct_le_windingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRankOneWindingTail.lean)
-/
@[path]
private lemma fkRectAugmentedSource_barrierConnectionProduct_le_windingTail_eq
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
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) ≤ fkRectCriticalWindingTailMass R q 1 := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSource_barrierConnectionProduct_le_windingTail R leftRight cut hsep hleft hq hgap x hx hchosen t hpair


-- created on 2026-10-23
