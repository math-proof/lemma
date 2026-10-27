import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-!
# Multivariable logarithmic Mahler measure

For a Laurent polynomial in `n` variables, this file defines evaluation on the unit torus and the
normalized integral of the logarithm of its norm. This is the formula in arXiv:2608.01951v1,
`MMP5_arxiv_v1.tex`, lines 139–146.
-/

/-- The real phase `∑ j, e j * θ j` associated to an exponent vector `e`. -/
def realSum (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℝ :=
  ∑ j, (e j : ℝ) * θ j

end MultivariableMahlerMeasure.MetaMathlibExt
end
