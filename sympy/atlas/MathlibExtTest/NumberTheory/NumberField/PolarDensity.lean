/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/PolarDensity.lean -/


import sympy.atlas.NumberTheory.NumberField.PolarDensity
import Lemma.Set.NumberField.PolarDensity


open Filter Topology NumberField IsDedekindDomain

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]

-- Destructure `HasPolarDensity` to expose `n`, `m`, `F` and all four conditions.
example (S : Set (HeightOneSpectrum (𝓞 K))) (ρ : ℚ)
    (h : S.HasPolarDensity ρ) :
    ∃ (n : ℕ+) (m : ℤ) (F : ℂ → ℂ), MeromorphicAt F (1 : ℂ) ∧
      F =ᶠ[nhdsWithin (1 : ℂ) {z : ℂ | (1 : ℝ) < z.re}]
        (fun s => NumberField.partialDedekindZeta K S s ^ (n : ℕ)) ∧
      meromorphicOrderAt F (1 : ℂ) = (↑(-m) : WithTop ℤ) ∧
      ρ = (m : ℚ) / (n : ℚ) := by
  obtain ⟨n, m, F, hmer, hcont, hord, hrat⟩ := h
  exact ⟨n, m, F, hmer, hcont, hord, hrat⟩

-- The empty set has polar density `0`.
example : (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity 0 :=
  hasPolarDensity_empty K

-- Polar densities of a fixed set agree.
example {S : Set (HeightOneSpectrum (𝓞 K))} {ρ₁ ρ₂ : ℚ}
    (h₁ : S.HasPolarDensity ρ₁) (h₂ : S.HasPolarDensity ρ₂) :
    ρ₁ = ρ₂ :=
  h₁.unique h₂

-- Any polar density of the empty set is zero.
example {ρ : ℚ} (h : (∅ : Set (HeightOneSpectrum (𝓞 K))).HasPolarDensity ρ) :
    ρ = 0 :=
  h.unique (hasPolarDensity_empty K)

end NumberField.Set
