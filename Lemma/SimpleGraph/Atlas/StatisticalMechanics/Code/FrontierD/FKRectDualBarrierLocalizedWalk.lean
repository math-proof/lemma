import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedWalk
open SimpleGraph StatMech StatMech.FrontierD


/--
[exists_fkRectForceDualPullbackUnitPattern_localizedVerticalWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierLocalizedWalk.lean)
-/
@[path]
private lemma exists_fkRectForceDualPullbackUnitPattern_localizedVerticalWalk_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 <= right)
  (hspans : FKRectColumnBandConnectionChainSpans R 1 right (fkRectUnitGapColumn R) (by rfl) hright t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega ∃ w : (fkRectOpenGraph R forced).Walk (fkRectRowOneVertex R (fkRectUnitGapColumn R)) (fkRectLastRowVertex R (fkRectUnitGapColumn R)), ∀ v ∈ w.support, 1 <= v.1.val ∧ v.1.val <= right ∧ 1 <= v.2.val ∧ v.2.val <= R.height - 1 := by
-- proof
  apply StatMech.FrontierD.exists_fkRectForceDualPullbackUnitPattern_localizedVerticalWalk R right hright omega t hspans haux


-- created on 2026-10-23
