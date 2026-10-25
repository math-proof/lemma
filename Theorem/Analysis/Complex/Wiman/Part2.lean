import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Def.Analysis.Complex.Wiman.Part3
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
