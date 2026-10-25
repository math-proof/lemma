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


end WindingDatum

end AutomorphicForm

end
