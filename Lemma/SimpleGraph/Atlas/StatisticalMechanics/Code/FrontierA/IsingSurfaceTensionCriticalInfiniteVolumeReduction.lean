import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalInfiniteVolumeReduction
open Filter Topology StatMech StatMech.FrontierA


/--
[cubicalInfiniteVolumeSquareWilsonDensity_le_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalInfiniteVolumeReduction.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeSquareWilsonDensity_le_central_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta)
  (hn : 0 < n) :
-- imply
  cubicalInfiniteVolumeSquareWilsonDensity (gaugeCriticalCoupling beta) (2 * n) <= centralCubicalIsingDisorderDensity beta n := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeSquareWilsonDensity_le_central hbeta n hn

/--
[rectangularIsingSurfaceTension_eq_zero_of_central_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalInfiniteVolumeReduction.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_eq_zero_of_central_tendsto_zero_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hcentral : Tendsto (centralCubicalIsingDisorderDensity beta) atTop (nhds 0)) :
-- imply
  rectangularIsingSurfaceTension beta = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_eq_zero_of_central_tendsto_zero hbeta hcentral

/--
[rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalInfiniteVolumeReduction.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_infinite_eq
-- given
  (hmean : forall n, OddPrismUnequalBridgeSymmetricMeanOrder (StatMech.Ising.betaC 3) n) :
-- imply
  rectangularIsingSurfaceTension (StatMech.Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_critical_eq_zero_of_symmetricMeanOrder_infinite hmean


-- created on 2026-10-23
