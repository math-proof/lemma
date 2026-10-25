import Mathlib
import Structure.AutomorphicForm_WindingDatum

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm


namespace WindingDatum

variable {r d c : ℕ} (𝒟 : WindingDatum r d c)

def fibreTerm (i : ℕ) (n : Fin d → ℤ) (γ : 𝒟.sub i) : ℂ :=
  if (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i = n then
    𝒟.Ψ i (𝒟.x₀ i + (γ : (Fin r → ℝ) × (Fin d → ℤ)).1) *
      ∏ j, fourier (𝒟.m i j) (𝒟.θ₀ i j + 𝒟.χ ⟨(γ : (Fin r → ℝ) × (Fin d → ℤ)), 𝒟.hsub i γ.2⟩ j)
  else 0

def fibreCoeff (i : ℕ) (n : Fin d → ℤ) : ℂ :=
  ∑' γ : 𝒟.sub i, 𝒟.fibreTerm i n γ

def coeff (n : Fin d → ℤ) : ℂ :=
  ∑' i : ℕ, 𝒟.lam i * 𝒟.fibreCoeff i n

theorem fibreTerm_of_ne (i : ℕ) (n : Fin d → ℤ) (γ : 𝒟.sub i)
    (h : (γ : (Fin r → ℝ) × (Fin d → ℤ)).2 + 𝒟.n₀ i ≠ n) : 𝒟.fibreTerm i n γ = 0 :=
  if_neg h

theorem coeff_eq_zero_of_lam_eq_zero (h : ∀ i : ℕ, 𝒟.lam i = 0) (n : Fin d → ℤ) : 𝒟.coeff n = 0 := by
  simp [coeff, h]

end WindingDatum

end AutomorphicForm

end
