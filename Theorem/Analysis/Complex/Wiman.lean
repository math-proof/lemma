import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Def.Analysis.Complex.Wiman.Part2
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

end
end Complex.Wiman
