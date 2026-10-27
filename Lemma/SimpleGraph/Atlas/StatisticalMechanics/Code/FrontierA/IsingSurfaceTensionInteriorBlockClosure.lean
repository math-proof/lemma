import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionInteriorBlockClosure
open Filter Topology StatMech StatMech.FrontierA


/--
[rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  rectangularIsingSurfaceTension (gaugeDualCoupling K) <= cubicalInfiniteVolumeSquareWilsonDensity K n := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_le_infiniteVolumeSquareWilsonDensity K hK n

/--
[rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
-- imply
  rectangularIsingSurfaceTension (gaugeDualCoupling K) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_eq_zero_of_dual_lt_betaC K hK hlt

/--
[cubicalFiniteInfiniteSquareDensityGap_tendsto_zero_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma cubicalFiniteInfiniteSquareDensityGap_tendsto_zero_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
-- imply
  Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.cubicalFiniteInfiniteSquareDensityGap_tendsto_zero_of_dual_lt_betaC K hK hlt

/--
[rectangularIsingSurfaceTension_eq_zero_of_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_eq_zero_of_lt_betaC_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hlt : beta < StatMech.Ising.betaC 3) :
-- imply
  rectangularIsingSurfaceTension beta = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_eq_zero_of_lt_betaC beta hbeta hlt

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_ne_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_ne_betaC_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hne : beta ≠ StatMech.Ising.betaC 3) :
-- imply
  0 < rectangularIsingSurfaceTension beta <-> StatMech.Ising.betaC 3 < beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_ne_betaC beta hbeta hne

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionInteriorBlockClosure.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero_eq
  {beta : Real}
-- given
  (hcritical : rectangularIsingSurfaceTension (StatMech.Ising.betaC 3) = 0)
  (hbeta : 0 < beta) :
-- imply
  0 < rectangularIsingSurfaceTension beta <-> StatMech.Ising.betaC 3 < beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_critical_zero hcritical beta hbeta


-- created on 2026-10-23
