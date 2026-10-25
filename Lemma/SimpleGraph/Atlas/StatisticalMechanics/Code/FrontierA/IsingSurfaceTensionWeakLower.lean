import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionWeakLower
open Filter Set Topology StatMech StatMech.FrontierA


/--
[pOfBeta_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionWeakLower.lean)
-/
@[path]
private lemma pOfBeta_mono_eq
  {a b : Real}
-- given
  (hab : a <= b) :
-- imply
  pOfBeta a <= pOfBeta b := by
-- proof
  apply StatMech.FrontierA.pOfBeta_mono hab

/--
[magnetization_monotoneOn_Ioi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionWeakLower.lean)
-/
@[path]
private lemma magnetization_monotoneOn_Ioi_eq
  {d : Nat}
-- given
  (hd : 1 <= d) :
-- imply
  MonotoneOn (magnetization d) (Ioi 0) := by
-- proof
  apply StatMech.FrontierA.magnetization_monotoneOn_Ioi d hd

/--
[standardCubicInterfaceDensity_hasWeakLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionWeakLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_hasWeakLowerBound_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  HasWeakSurfaceTensionLowerBound 1 (magnetization 3) (fun beta => standardCubicInterfaceDensity beta n) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_hasWeakLowerBound n hn

/--
[rectangularIsingSurfaceTension_hasWeakLowerBound_of_prismComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionWeakLower.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_hasWeakLowerBound_of_prismComparison_eq
-- given
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta) :
-- imply
  HasWeakSurfaceTensionLowerBound 1 (magnetization 3) rectangularIsingSurfaceTension := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_hasWeakLowerBound_of_prismComparison hprism


-- created on 2026-10-23
