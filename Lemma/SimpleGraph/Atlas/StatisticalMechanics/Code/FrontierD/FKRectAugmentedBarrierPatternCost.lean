import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
open StatMech StatMech.FrontierD


/--
[fkRectNoLeftStripCrossing_dependsOnOutside_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierPatternCost.lean)
-/
@[path]
private lemma fkRectNoLeftStripCrossing_dependsOnOutside_attachment_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {x : Fin R.width}
-- given
  (hx : leftRight < x.val) :
-- imply
  FKRectDependsOnOutsideEdges R {fkRectRowZeroAttachmentEdgeAt R x} (fkRectNoLeftStripCrossingEvent R leftRight) := by
-- proof
  apply StatMech.FrontierD.fkRectNoLeftStripCrossing_dependsOnOutside_attachment R leftRight x hx

/--
[fkRectSourceLeftBarrier_dependsOnOutside_attachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierPatternCost.lean)
-/
@[path]
private lemma fkRectSourceLeftBarrier_dependsOnOutside_attachment_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
-- given
  (hx : leftRight < x.val) :
-- imply
  FKRectDependsOnOutsideEdges R {fkRectRowZeroAttachmentEdgeAt R x} (fkRectSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.fkRectSourceLeftBarrier_dependsOnOutside_attachment R leftRight gap x hx

/--
[fkRectAugmentedSourceBarrier_eq_attachment_inter_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierPatternCost.lean)
-/
@[path]
private lemma fkRectAugmentedSourceBarrier_eq_attachment_inter_source_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width} :
-- imply
  fkRectAugmentedSourceBarrier R leftRight gap x = fkRectIndexedPatternEvent R {fkRectRowZeroAttachmentEdgeAt R x} (fkRectAllButOneOpenConfiguration R gap) ∩ fkRectSourceLeftBarrier R leftRight gap := by
-- proof
  apply StatMech.FrontierD.fkRectAugmentedSourceBarrier_eq_attachment_inter_source R leftRight gap x

/--
[fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedBarrierPatternCost.lean)
-/
@[path]
private lemma fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex}
  {x : Fin R.width}
  {q : Real}
-- given
  (hx : leftRight < x.val)
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) ≤ fkRectCriticalEventMass R q (fkRectAugmentedSourceBarrier R leftRight gap x) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_mul_sourceBarrier_le_augmentedSourceBarrier R leftRight gap x hx hq


-- created on 2026-10-23
