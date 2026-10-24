import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectLocalizedVerticalCycle_mem_dualPreimage_noLeftStripCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierForceTopology.lean)
-/
@[path]
private lemma fkRectLocalizedVerticalCycle_mem_dualPreimage_noLeftStripCrossing_eq
  {R : FKRectTorus}
  {right : Nat}
  {forced : R.Configuration}
  {z : (fkRectOpenGraph R forced).Walk (fkRectRowOneVertex R (fkRectUnitGapColumn R)) (fkRectRowOneVertex R (fkRectUnitGapColumn R))}
-- given
  (hright : 1 ≤ right)
  (hproper : right + 1 < R.width)
  (hzWinding : fkRectWalkWinding R z = (0, 1))
  (hzSupport : ∀ v ∈ z.support, 1 ≤ v.1.val ∧ v.1.val ≤ right) :
-- imply
  forced ∈ fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R right) := by
-- proof
  apply StatMech.FrontierD.fkRectLocalizedVerticalCycle_mem_dualPreimage_noLeftStripCrossing R right hright hproper forced z hzWinding hzSupport

/--
[fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierForceTopology.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 ≤ right)
  (hproper : right + 1 < R.width)
  (hspans : FKRectColumnBandConnectionChainSpans R 1 right (fkRectUnitGapColumn R) (by rfl) hright t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega forced ∈ fkRectDualPreimageEvent R (fkRectNoLeftStripCrossingEvent R right) := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_mem_dualPreimage_noLeftStripCrossing R right hright hproper omega t hspans haux


-- created on 2026-10-23
