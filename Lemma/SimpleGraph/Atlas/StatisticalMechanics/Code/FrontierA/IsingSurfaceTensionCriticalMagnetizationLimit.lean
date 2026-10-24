import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalMagnetizationLimit
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[magnetization_three_tendsto_at_isingBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalMagnetizationLimit.lean)
-/
@[path]
private lemma magnetization_three_tendsto_at_isingBetaC_eq
-- given
  (betaSeq : Nat -> Real)
  (hbeta : Tendsto betaSeq atTop (nhds (Ising.betaC 3))) :
-- imply
  Tendsto (fun k => magnetization 3 (betaSeq k)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.magnetization_three_tendsto_at_isingBetaC betaSeq hbeta

/--
[rectangularIsingSurfaceTension_critical_eq_zero_of_ordered_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCriticalMagnetizationLimit.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_critical_eq_zero_of_ordered_upper_eq
-- given
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta)
  (hupper : forall beta, Ising.betaC 3 < beta -> rectangularIsingSurfaceTension beta <= 2 * beta * (magnetization 3 beta) ^ 2) :
-- imply
  rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_critical_eq_zero_of_ordered_upper hprism hupper


-- created on 2026-10-23
