import Mathlib
import sympy.Basic
open Polynomial


private lemma derivative_Ψ₃ {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
  derivative W.Ψ₃ = 12 * X ^ 3 + 3 * C W.b₂ * X ^ 2 + 6 * C W.b₄ * X + 3 * C W.b₆ := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [derivative_add, derivative_mul, derivative_ofNat, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, zero_add, mul_one, add_zero]
  simp only [Nat.cast_ofNat, map_ofNat, Nat.add_one_sub_one, pow_one]
  ring

private lemma psi3_bezout {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
  (-144 * X ^ 2 - 24 * C W.b₂ * X + 3 * C (W.b₂ ^ 2 - 32 * W.b₄)) * W.Ψ₃ +
    (36 * X ^ 3 + 9 * C W.b₂ * X ^ 2 + C (42 * W.b₄ - W.b₂ ^ 2) * X + C (27 * W.b₆ - W.b₂ * W.b₄)) *
      derivative W.Ψ₃ = C (-3 * W.Δ) := by
  rw [derivative_Ψ₃, WeierstrassCurve.Ψ₃]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
  ring

private lemma separable_psi3 {K : Type*} [Field K] (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
  (h3 : (3 : K) ≠ 0) : W.Ψ₃.Separable := by
  rw [separable_def']
  have h : (-3 * W.Δ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h3) hΔ
  have hk : C (-3 * W.Δ)⁻¹ * C (-3 * W.Δ) = 1 := by rw [← C_mul, inv_mul_cancel₀ h, C_1]
  refine ⟨C (-3 * W.Δ)⁻¹ * (-144 * X ^ 2 - 24 * C W.b₂ * X + 3 * C (W.b₂ ^ 2 - 32 * W.b₄)),
    C (-3 * W.Δ)⁻¹ * (36 * X ^ 3 + 9 * C W.b₂ * X ^ 2 + C (42 * W.b₄ - W.b₂ ^ 2) * X +
      C (27 * W.b₆ - W.b₂ * W.b₄)), by linear_combination (C (-3 * W.Δ)⁻¹) * psi3_bezout W + hk⟩
/--
[WeierstrassCurve_separable_Psi3](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_separable_Psi3.lean)
-/
@[path]
private lemma main
  [Field K]
  {W : WeierstrassCurve K}
-- given
  (hΔ : W.Δ ≠ 0)
  (h0 : (3 : K) ≠ 0) :
-- imply
  W.Ψ₃.Separable :=
-- proof
  separable_psi3 W hΔ h0


-- created on 2026-10-23
