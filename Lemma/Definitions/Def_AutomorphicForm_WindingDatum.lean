import Mathlib

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm

structure WindingDatum (r d c : ℕ) where

  Λ : AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))

  hΛ : DiscreteTopology Λ

  s : (Fin r → ℝ) →ₗ[ℝ] ℝ

  ω : Fin d → ℝ

  hω : ω ≠ 0

  hpf : ∀ x ∈ Λ, s x.1 = ∑ i, ω i * (x.2 i : ℝ)

  χ : Λ →+ (Fin c → AddCircle (1 : ℝ))

  sub : ℕ → AddSubgroup ((Fin r → ℝ) × (Fin d → ℤ))

  hsub : ∀ i : ℕ, sub i ≤ Λ

  Ψ : ℕ → (Fin r → ℝ) → ℂ

  hΨc : ∀ i : ℕ, Continuous (Ψ i)

  hΨi : ∀ i : ℕ, Integrable (Ψ i)

  C : ℕ → ℝ

  hΨd : ∀ (i : ℕ) (x : Fin r → ℝ), ‖Ψ i x‖ ≤ C i * ∏ k, (1 + |x k|)⁻¹ ^ 2

  hΨhatd : ∀ (i : ℕ) (ξ : Fin r → ℝ),
    ‖∫ x : Fin r → ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((∑ k, ξ k * x k : ℝ) : ℂ))) * Ψ i x‖ ≤
      C i * ∏ k, (1 + |ξ k|)⁻¹ ^ 2

  m : ℕ → Fin c → ℤ

  θ₀ : ℕ → Fin c → AddCircle (1 : ℝ)

  x₀ : ℕ → Fin r → ℝ

  n₀ : ℕ → Fin d → ℤ

  lam : ℕ → ℂ

  hsum : Summable fun i : ℕ => ‖lam i‖ * C i

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
