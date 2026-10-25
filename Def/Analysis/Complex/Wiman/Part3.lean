import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.TaylorSeries
import Theorem.Analysis.Complex.Wiman
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

/-- A complex function is transcendental when it is not represented by a complex polynomial.
Analytic regularity is recorded separately by callers. -/
def IsTranscendental (f : ℂ → ℂ) : Prop :=
  ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z

end
end Complex.Wiman
