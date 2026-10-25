import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm.GL2Twisted

def unitaryElt (ψ η ξ₁ ξ₂ : ℝ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have h2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have h3 : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq η
      have hE : Complex.exp (ψ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have key : Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)) *
            (Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))) -
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I)) *
            (Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I))))) =
          Complex.exp (ψ * Complex.I) ^ 2 := by
        linear_combination
          Complex.exp (ψ * Complex.I) ^ 2 * (Real.cos η : ℂ) ^ 2 * h1 +
            Complex.exp (ψ * Complex.I) ^ 2 * (Real.sin η : ℂ) ^ 2 * h2 +
            Complex.exp (ψ * Complex.I) ^ 2 * h3
      rw [key]
      exact pow_ne_zero 2 hE)

def unitaryAverage (F : GL (Fin 2) ℂ → ℂ) : ℂ :=
  (1 / (4 * Real.pi ^ 3) : ℂ) *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)

def conjEntries (g : GL (Fin 2) ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map (starRingEnd ℂ) g

def twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : (Real.sqrt a₁ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr h.1).ne'
      have h2 : (Real.sqrt a₂ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr h.2).ne'
      simpa using mul_ne_zero h1 h2)

def twistedSplitTransform (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  if h : 0 < a₁ ∧ 0 < a₂ then
    ∫ v : ℂ, unitaryAverage fun k => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k)
  else 0

def twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
        (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
          (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
      (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
        (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))]
    (by
      rw [Matrix.det_fin_two_of]
      have hE : Complex.exp (θ / 2 * Complex.I) * Complex.exp (-(θ / 2 * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      have hρi : (ρ : ℂ)⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ'
      have hu : (starRingEnd ℂ) u * u = (Complex.normSq u : ℂ) := by
        rw [mul_comm]; exact Complex.mul_conj u
      have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
      have key : (Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) *
            ((Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) -
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I))) *
            ((Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I)))) = -(r : ℂ) := by
        linear_combination
          (-(ρ : ℂ) ^ 2 * Complex.exp (-(θ / 2 * Complex.I)) ^ 2 * (Real.sqrt r : ℂ) ^ 2) * hu -
            (Real.sqrt r : ℂ) ^ 2 * hρi - (Real.sqrt r : ℂ) ^ 2 * ((ρ : ℂ)⁻¹ * ρ) * hE - hs
      rw [key]
      exact neg_ne_zero.mpr (by exact_mod_cast hr.ne'))

def twistedEllipticTransform (φ : GL (Fin 2) ℂ → ℂ) (r θ : ℝ) : ℂ :=
  if hr : 0 < r then
    (4 * Real.sin θ ^ 2 : ℂ) *
      (∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ *
            ((unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries k)) +
              (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r (-θ) ρ u hr hρ * conjEntries k)))
        else 0)
  else 0

end AutomorphicForm.GL2Twisted

end
