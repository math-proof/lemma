import Lemma.ModularCurve.PeriodMap
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Def.ModularCurve_PeriodMapBundled

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups


theorem periodMap_def (N : ℕ) (f : CuspForm (Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : HasEquivariantPrimitive N f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitive N f F₀), periodMap N f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dif_pos h⟩

end ModularCurve
