import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
open Filter Set Topology StatMech StatMech.FrontierA


/--
[magnetization_three_isingBetaC_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalReduction.lean)
-/
@[path]
private lemma magnetization_three_isingBetaC_eq_zero_eq :
-- imply
  magnetization 3 (Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.magnetization_three_isingBetaC_eq_zero

/--
[rectangularIsingSurfaceTension_critical_eq_zero_of_asymptotic_standard_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalReduction.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_critical_eq_zero_of_asymptotic_standard_upper_eq
-- given
  (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
  (hupper : forall eps, 0 < eps -> Filter.Eventually (fun n => standardCubicInterfaceDensity (Ising.betaC 3) n <= 2 * Ising.betaC 3 * (magnetization 3 (Ising.betaC 3)) ^ 2 + eps) atTop) :
-- imply
  rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_critical_eq_zero_of_asymptotic_standard_upper hprism hupper


-- created on 2026-10-23
