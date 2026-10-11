import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The Wiman maximum-term theorem

This file fixes the Taylor-coefficient, maximum-term, and maximum-modulus
normalizations used by the Wiman route. A strict unbounded-radius corollary of
the classical Wiman-Valiron inequality quoted by Filevych (2003), specialized
to transcendental entire functions and exponent `2 / 3`, is proved in
`MathlibExt.Analysis.Complex.Wiman.Filevych`.
-/

namespace Complex.Wiman

noncomputable section

open Complex Set

/-- The Taylor coefficient of an entire function at the origin. -/
def wimanTaylorCoefficient (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (n.factorial : ℂ)

/-- The modulus of the `n`th Taylor term at radius `|r|`.

Normalizing at the definition boundary makes negative inputs denote the same radius as their
absolute values, so this quantity is always nonnegative. -/
def wimanTerm (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : ℝ :=
  ‖wimanTaylorCoefficient f n‖ * |r| ^ n

/-- The maximum term, initially expressed as a supremum over all indices. -/
def wimanMaximumTerm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (range (wimanTerm f r))

/-- The maximum modulus on the circle of radius `|r|`. -/
def wimanMaximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖f z‖) '' Metric.sphere 0 |r|)

/-- Re-normalizing a Wiman term's radius does not change it. -/
@[simp]
theorem wimanTerm_abs (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    wimanTerm f |r| n = wimanTerm f r n := by
  simp [wimanTerm]

/-- Re-normalizing the radius does not change the maximum Taylor term. -/
@[simp]
theorem wimanMaximumTerm_abs (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumTerm f |r| = wimanMaximumTerm f r := by
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_abs f r n

/-- Re-normalizing the radius does not change the maximum modulus. -/
@[simp]
theorem wimanMaximumModulus_abs (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumModulus f |r| = wimanMaximumModulus f r := by
  simp [wimanMaximumModulus]

/-- Negating a radius does not change its Wiman term. -/
@[simp]
theorem wimanTerm_neg (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    wimanTerm f (-r) n = wimanTerm f r n := by
  simp [wimanTerm]

/-- Negating a radius does not change the maximum Taylor term. -/
@[simp]
theorem wimanMaximumTerm_neg (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumTerm f (-r) = wimanMaximumTerm f r := by
  apply congrArg sSup
  apply congrArg Set.range
  funext n
  exact wimanTerm_neg f r n

/-- Negating a radius does not change the maximum modulus. -/
@[simp]
theorem wimanMaximumModulus_neg (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumModulus f (-r) = wimanMaximumModulus f r := by
  simp [wimanMaximumModulus]

/-- A complex function is transcendental when it is not represented by a complex polynomial.
Analytic regularity is recorded separately by callers. -/
def IsTranscendental (f : ℂ → ℂ) : Prop :=
  ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z

/-- Every value on the circle is bounded by the supremum used for the Wiman
maximum modulus. -/
theorem norm_le_wimanMaximumModulus {f : ℂ → ℂ} {r : ℝ} {z : ℂ}
    (hf : Continuous f) (hz : ‖z‖ = r) :
    ‖f z‖ ≤ wimanMaximumModulus f r := by
  have hr : 0 ≤ r := hz ▸ norm_nonneg z
  apply le_csSup
  · exact (isCompact_sphere (0 : ℂ) |r|).bddAbove_image
      ((continuous_norm.comp hf).continuousOn)
  · exact ⟨z, by simpa [Metric.mem_sphere, abs_of_nonneg hr] using hz, rfl⟩

/-- Cubing removes the fractional exponent in a Wiman `2/3` bound. -/
theorem cube_le_cube_mul_log_sq_of_wiman {M μ : ℝ}
    (hM : 0 ≤ M) (_hμ : 0 ≤ μ) (hlog : 0 ≤ Real.log μ)
    (hWiman : M ≤ μ * Real.log μ ^ (2 / 3 : ℝ)) :
    M ^ 3 ≤ μ ^ 3 * Real.log μ ^ 2 := by
  calc
    M ^ 3 ≤ (μ * Real.log μ ^ (2 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hM hWiman 3
    _ = μ ^ 3 * (Real.log μ ^ (2 / 3 : ℝ)) ^ 3 := by
      rw [mul_pow]
    _ = μ ^ 3 * Real.log μ ^ 2 := by
      congr 1
      rw [← Real.rpow_mul_natCast hlog]
      norm_num [Real.rpow_two]

end

end Complex.Wiman
