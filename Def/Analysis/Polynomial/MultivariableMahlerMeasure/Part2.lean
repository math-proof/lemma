module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure

@[expose] public section

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
