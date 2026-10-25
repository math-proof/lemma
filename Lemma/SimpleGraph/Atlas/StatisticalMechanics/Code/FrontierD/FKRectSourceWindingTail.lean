import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceWindingTail
open StatMech StatMech.FrontierD


/--
[fkRectSource_barrierConnectionProduct_le_windingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceWindingTail.lean)
-/
@[path]
private lemma fkRectSource_barrierConnectionProduct_le_windingTail_eq
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
  FK.cFE (fkRectCriticalP q) q * (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) ≤ fkRectCriticalWindingTailMass R q 1 := by
-- proof
  apply StatMech.FrontierD.fkRectSource_barrierConnectionProduct_le_windingTail R leftRight cut hsep hleft hq hgap x hx hchosen t hpair


-- created on 2026-10-23
