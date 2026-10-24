import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.FinalAssembly
open StatMech StatMech.Onsager


/--
[ons_free_energy_of_spinKacWard_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FinalAssembly.lean)
-/
@[path]
private lemma ons_free_energy_of_spinKacWard_all_eq
  {beta : ℝ}
-- given
  (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
  (hbeta : 0 ≤ beta) :
-- imply
  Filter.Tendsto (ons_torusPressureSeq beta) Filter.atTop (nhds (ons_pressure beta)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy_of_spinKacWard_all hall beta hbeta

/--
[ons_KacWardResidue_of_spinKacWard_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FinalAssembly.lean)
-/
@[path]
private lemma ons_KacWardResidue_of_spinKacWard_all_eq
  {beta : ℝ}
-- given
  (hall : ∀ beta : ℝ, ons_spinKacWardIdentities beta)
  (hbeta : 0 ≤ beta) :
-- imply
  ons_KacWardResidue beta := by
-- proof
  apply StatMech.Onsager.ons_KacWardResidue_of_spinKacWard_all hall beta hbeta


-- created on 2026-10-23
