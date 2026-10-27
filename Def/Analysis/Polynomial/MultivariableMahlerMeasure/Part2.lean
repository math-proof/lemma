import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-- The torus character `e ↦ exp (I * ∑ j, e j * θ j)` at the angle vector `θ`. -/
def torusCharacter (θ : Fin n → ℝ) (e : Fin n → ℤ) : ℂ :=
  Complex.exp (Complex.I * (realSum θ e : ℂ))

end MultivariableMahlerMeasure.MetaMathlibExt
end
