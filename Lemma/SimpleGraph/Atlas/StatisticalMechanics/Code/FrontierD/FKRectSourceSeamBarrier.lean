import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier
open StatMech StatMech.FrontierD


/--
[fkRectHorizontalCutEdge_crossesVerticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectHorizontalCutEdge_crossesVerticalSeam_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ fkRectHorizontalCutEdges R) :
-- imply
  fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCutEdge_crossesVerticalSeam R a ha

/--
[mem_fkRectAllButOneOpenSeamEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma mem_fkRectAllButOneOpenSeamEvent_iff_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration} :
-- imply
  omega ∈ fkRectAllButOneOpenSeamEvent R gap ↔ ∀ a ∈ fkRectHorizontalCutEdges R, omega a = decide (a ≠ gap) := by
-- proof
  apply StatMech.FrontierD.mem_fkRectAllButOneOpenSeamEvent_iff R gap omega

/--
[fkRectAllButOneOpenSeamEvent_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectAllButOneOpenSeamEvent_open_iff_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap)
  (ha : a ∈ fkRectHorizontalCutEdges R) :
-- imply
  omega a = true ↔ a ≠ gap := by
-- proof
  apply StatMech.FrontierD.fkRectAllButOneOpenSeamEvent_open_iff R homega ha

/--
[fkRectAllButOneOpenSeamEvent_gap_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectAllButOneOpenSeamEvent_gap_closed_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex}
  {omega : R.Configuration}
-- given
  (hgap : gap ∈ fkRectHorizontalCutEdges R)
  (homega : omega ∈ fkRectAllButOneOpenSeamEvent R gap) :
-- imply
  omega gap = false := by
-- proof
  apply StatMech.FrontierD.fkRectAllButOneOpenSeamEvent_gap_closed R hgap homega

/--
[fkRectSourceLeftBarrier_eq_generic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectSourceLeftBarrier_eq_generic_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex} :
-- imply
  fkRectSourceLeftBarrier R leftRight gap = fkRectLeftBarrierWithSeamPattern R leftRight (fkRectHorizontalCutEdges R) (fkRectAllButOneOpenConfiguration R gap) := by
-- proof
  apply StatMech.FrontierD.fkRectSourceLeftBarrier_eq_generic R leftRight gap

/--
[fkRectSourceLeftBarrier_dependsOnOutsideRightStripBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectSourceLeftBarrier_dependsOnOutsideRightStripBand_eq
  {R : FKRectTorus}
  {leftRight cut lower upper : Nat}
  {gap : R.EdgeIndex}
-- given
  (hsep : leftRight < cut)
  (hlower : 1 ≤ lower) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut lower upper) (fkRectSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.fkRectSourceLeftBarrier_dependsOnOutsideRightStripBand R leftRight cut lower upper hsep hlower gap

/--
[fkRectSource_barrierConnectionProduct_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean)
-/
@[path]
private lemma fkRectSource_barrierConnectionProduct_le_eq
  {R : FKRectTorus}
  {leftRight cut lower upper : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {t : Finset (FKRectRightStripBandVertex R cut lower upper × FKRectRightStripBandVertex R cut lower upper)}
-- given
  (hsep : leftRight < cut)
  (hlower : 1 ≤ lower)
  (hq : 1 ≤ q) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) ≤ ∑ rho, (fkRectSourceBarrierConnectionEvent R leftRight cut lower upper gap t).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectSource_barrierConnectionProduct_le R leftRight cut lower upper hsep hlower hq gap t


-- created on 2026-10-23
