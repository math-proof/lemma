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

end
end Complex.Wiman
