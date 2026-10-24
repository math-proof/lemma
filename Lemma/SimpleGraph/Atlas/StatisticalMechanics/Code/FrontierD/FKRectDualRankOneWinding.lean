import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
open StatMech StatMech.FrontierD


/--
[fkRectVerticalRankOne_dualPreimageAllButOne_subset_windingOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualRankOneWinding.lean)
-/
@[path]
private lemma fkRectVerticalRankOne_dualPreimageAllButOne_subset_windingOne_eq
  {R : FKRectTorus}
  {gap : R.EdgeIndex} :
-- imply
  fkRectVerticalRankOneEvent R ∩ fkRectDualPreimageEvent R (fkRectAllButOneOpenSeamEvent R gap) ⊆ {omega | fkRectUnorientedVerticalWindingNumber R omega = 1} := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalRankOne_dualPreimageAllButOne_subset_windingOne R gap

/--
[fkRectForceDualPullbackUnitPattern_windingOne_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualRankOneWinding.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_windingOne_of_not_hasNet_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 ≤ right)
  (hproper : right + 1 < R.width)
  (hspans : FKRectColumnBandConnectionChainSpans R 1 right (fkRectUnitGapColumn R) (by rfl) hright t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega)
  (hnoNet : let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega ¬ FKRectHasNet R forced) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega fkRectUnorientedVerticalWindingNumber R forced = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_windingOne_of_not_hasNet R right hright hproper omega t hspans haux hnoNet


-- created on 2026-10-23
