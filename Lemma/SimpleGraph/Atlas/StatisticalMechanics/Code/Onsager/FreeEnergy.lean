import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.FreeEnergy
open StatMech StatMech.Onsager


/--
[ons_torusPressure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FreeEnergy.lean)
-/
@[path]
private lemma ons_torusPressure_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  ons_pressureFinite (onsTorusGraph L) β = Real.log 2 + 2 * Real.log (Real.cosh β) + Real.log (ons_X (onsTorusGraph L) (Real.tanh β)) / ((L : ℝ) ^ 2) := by
-- proof
  apply StatMech.Onsager.ons_torusPressure_eq L β hβ

/--
[ons_free_energy_of_KacWardResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/FreeEnergy.lean)
-/
@[path]
private lemma ons_free_energy_of_KacWardResidue_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hres : ons_KacWardResidue β) :
-- imply
  Filter.Tendsto (fun L : ℕ => if h : 2 < L then (letI : Fact (2 < L) := ⟨h⟩; ons_pressureFinite (onsTorusGraph L) β) else 0) Filter.atTop (nhds (ons_pressure β)) := by
-- proof
  apply StatMech.Onsager.ons_free_energy_of_KacWardResidue β hβ hres


-- created on 2026-10-23
