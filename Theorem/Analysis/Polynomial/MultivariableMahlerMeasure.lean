module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Def.Analysis.Polynomial.MultivariableMahlerMeasure
open Complex MeasureTheory Finset
open scoped Real

public section

noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

@[simp]
theorem realSum_zero (θ : Fin n → ℝ) : realSum θ 0 = 0 := by
  simp [realSum]

theorem realSum_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    realSum θ (a + b) = realSum θ a + realSum θ b := by
  simp only [realSum, Pi.add_apply, Int.cast_add, add_mul, sum_add_distrib]

end MultivariableMahlerMeasure.MetaMathlibExt
end
