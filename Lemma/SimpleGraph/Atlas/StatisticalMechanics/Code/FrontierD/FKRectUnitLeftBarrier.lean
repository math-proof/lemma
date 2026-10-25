import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectUnitLeftBarrierGap_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierGap_mem_eq
  {R : FKRectTorus} :
-- imply
  fkRectUnitLeftBarrierGap R ∈ fkRectHorizontalCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierGap_mem R

/--
[fkRectUnitLeftBarrierConfiguration_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierConfiguration_seam_eq
  {R : FKRectTorus} :
-- imply
  fkRectUnitLeftBarrierConfiguration R ∈ fkRectAllButOneOpenSeamEvent R (fkRectUnitLeftBarrierGap R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierConfiguration_seam R

/--
[fkRectUnitLeftBarrier_inducedAdj_column_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrier_inducedAdj_column_eq_eq
  {R : FKRectTorus}
  {u v : fkRectLeftStrip R 1}
-- given
  (huv : ((fkRectOpenGraph R (fkRectUnitLeftBarrierConfiguration R)).induce (fkRectLeftStrip R 1)).Adj u v) :
-- imply
  u.1.1.val = v.1.1.val := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrier_inducedAdj_column_eq R huv

/--
[fkRectUnitLeftBarrier_inducedAdj_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrier_inducedAdj_zero_iff_eq
  {R : FKRectTorus}
  {right : Nat}
  {u v : fkRectLeftStrip R right}
-- given
  (hright : right + 1 < R.width)
  (huv : ((fkRectOpenGraph R (fkRectUnitLeftBarrierConfiguration R)).induce (fkRectLeftStrip R right)).Adj u v) :
-- imply
  u.1.1.val = 0 ↔ v.1.1.val = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrier_inducedAdj_zero_iff R right hright huv

/--
[fkRectUnitLeftBarrierConfiguration_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierConfiguration_noCrossing_eq
  {R : FKRectTorus} :
-- imply
  fkRectUnitLeftBarrierConfiguration R ∈ fkRectNoLeftStripCrossingEvent R 1 := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierConfiguration_noCrossing R

/--
[fkRectUnitLeftBarrierConfiguration_noCrossing_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierConfiguration_noCrossing_of_one_le_eq
  {R : FKRectTorus}
  {right : Nat}
-- given
  (hone : 1 <= right)
  (hright : right + 1 < R.width) :
-- imply
  fkRectUnitLeftBarrierConfiguration R ∈ fkRectNoLeftStripCrossingEvent R right := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierConfiguration_noCrossing_of_one_le R right hone hright

/--
[fkRectUnitLeftBarrierConfiguration_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierConfiguration_mem_source_eq
  {R : FKRectTorus} :
-- imply
  fkRectUnitLeftBarrierConfiguration R ∈ fkRectSourceLeftBarrier R 1 (fkRectUnitLeftBarrierGap R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierConfiguration_mem_source R

/--
[fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean)
-/
@[path]
private lemma fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le_eq
  {R : FKRectTorus}
  {right : Nat}
-- given
  (hone : 1 <= right)
  (hright : right + 1 < R.width) :
-- imply
  fkRectUnitLeftBarrierConfiguration R ∈ fkRectSourceLeftBarrier R right (fkRectUnitLeftBarrierGap R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le R right hone hright


-- created on 2026-10-23
