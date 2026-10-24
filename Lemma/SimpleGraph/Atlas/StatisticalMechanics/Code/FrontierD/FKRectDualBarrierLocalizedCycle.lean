import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectWalkWinding_eq_zero_of_support_in_positiveColumnBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierLocalizedCycle.lean)
-/
@[path]
private lemma fkRectWalkWinding_eq_zero_of_support_in_positiveColumnBand_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R omega).Walk x y}
-- given
  (_hright : right + 1 < R.width)
  (hsupport : ∀ v ∈ w.support, 1 <= v.1.val ∧ v.1.val <= right ∧ 1 <= v.2.val ∧ v.2.val <= R.height - 1) :
-- imply
  fkRectWalkWinding R w = (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_eq_zero_of_support_in_positiveColumnBand R right _hright w hsupport

/--
[exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierLocalizedCycle.lean)
-/
@[path]
private lemma exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 <= right)
  (hproper : right + 1 < R.width)
  (hspans : FKRectColumnBandConnectionChainSpans R 1 right (fkRectUnitGapColumn R) (by rfl) hright t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega ∃ z : (fkRectOpenGraph R forced).Walk (fkRectRowOneVertex R (fkRectUnitGapColumn R)) (fkRectRowOneVertex R (fkRectUnitGapColumn R)), fkRectWalkWinding R z = (0, 1) ∧ ∀ v ∈ z.support, 1 <= v.1.val ∧ v.1.val <= right := by
-- proof
  apply StatMech.FrontierD.exists_fkRectForceDualPullbackUnitPattern_localizedVerticalCycle R right hright hproper omega t hspans haux


-- created on 2026-10-23
