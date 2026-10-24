/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/QuantumInformation/Finite/TsirelsonTight.lean -/


import sympy.atlas.QuantumInformation.Finite.TsirelsonTight
import Lemma.Matrix.Finite.TsirelsonTight

namespace MetaMathlibExt

open MathlibExt.QuantumInformation.Finite.TsirelsonTight

/-- Exact-statement exercise of the migrated public API. -/
example :
    ∃ (A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℂ),
      IsCHSHTuple A₀ A₁ B₀ B₁ ∧
        Module.End.HasEigenvalue
          (Matrix.toLin' (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁))
          ((↑(2 * Real.sqrt 2) : ℂ)) :=
  tsirelson_bound_tight

/-- Focused smoke check: the witnessed eigenvalue has a nontrivial eigenspace. -/
example :
    ∃ (A₀ A₁ B₀ B₁ : Matrix (Fin 4) (Fin 4) ℂ),
      IsCHSHTuple A₀ A₁ B₀ B₁ ∧
        Module.End.eigenspace
          (Matrix.toLin' (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁))
          ((↑(2 * Real.sqrt 2) : ℂ)) ≠ ⊥ := by
  obtain ⟨A₀, A₁, B₀, B₁, hT, hEig⟩ := tsirelson_bound_tight
  exact ⟨A₀, A₁, B₀, B₁, hT, (Module.End.hasEigenvalue_iff).mp hEig⟩

end MetaMathlibExt
