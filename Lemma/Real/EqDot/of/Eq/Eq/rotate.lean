import Mathlib.Analysis.Complex.Trigonometric
import sympy.Basic


@[path]
private lemma main
  {x₀ y₀ x₁ y₁ x₂ y₂ θ : ℝ}
  (h₀ :
    ((x₂ - x₀ : ℂ) + (y₂ - y₀) * Complex.I) =
      ((x₁ - x₀ : ℂ) + (y₁ - y₀) * Complex.I) * Complex.exp (Complex.I * θ)) :
-- imply
  x₂ - x₀ = (x₁ - x₀) * Real.cos θ - (y₁ - y₀) * Real.sin θ ∧
    y₂ - y₀ = (x₁ - x₀) * Real.sin θ + (y₁ - y₀) * Real.cos θ := by
-- proof
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring] at h₀
  rw [Complex.exp_mul_I] at h₀
  have hre := congrArg Complex.re h₀
  have him := congrArg Complex.im h₀
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re] at hre him
  constructor
  · apply hre
  · apply him


-- created on 2022-07-02
-- updated on 2026-10-17
