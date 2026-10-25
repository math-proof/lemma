import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionMeanfieldLower
open Filter Set Topology StatMech StatMech.FrontierA


/--
[standardCubicInterfaceDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionMeanfieldLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_nonneg_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  0 <= standardCubicInterfaceDensity beta n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_nonneg hbeta n hn

/--
[standardCubicInterfaceDensity_ge_meanfield_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionMeanfieldLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_ge_meanfield_increment_eq
  {betaC a beta : Real}
  {n : Nat}
-- given
  (hbetaC : 0 < betaC)
  (hsharp : forall gamma, betaC <= gamma -> Real.sqrt (1 - (betaC / gamma) ^ 2) <= magnetization 3 gamma)
  (ha : betaC < a)
  (hab : a < beta)
  (hn : 0 < n) :
-- imply
  2 * (Real.sqrt (1 - (betaC / a) ^ 2)) ^ 2 * (beta - a) <= standardCubicInterfaceDensity beta n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_ge_meanfield_increment hbetaC hsharp ha hab n hn

/--
[rectangularIsingSurfaceTension_pos_of_prismComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionMeanfieldLower.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_of_prismComparison_eq
  {beta : Real}
-- given
  (hcritical : betaC 3 < beta)
  (hprism : HasPrismCubicalSurfaceComparison beta) :
-- imply
  0 < rectangularIsingSurfaceTension beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_of_prismComparison hcritical hprism


-- created on 2026-10-23
