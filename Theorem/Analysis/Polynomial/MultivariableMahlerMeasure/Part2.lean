module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Def.Analysis.Polynomial.MultivariableMahlerMeasure.Part2
open Complex MeasureTheory Finset
open scoped Real

public section

noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

@[simp]
theorem torusCharacter_zero (θ : Fin n → ℝ) : torusCharacter θ 0 = 1 := by
  simp [torusCharacter]

theorem torusCharacter_add (θ : Fin n → ℝ) (a b : Fin n → ℤ) :
    torusCharacter θ (a + b) = torusCharacter θ a * torusCharacter θ b := by
  simp only [torusCharacter, realSum_add, Complex.ofReal_add, mul_add, Complex.exp_add]

end MultivariableMahlerMeasure.MetaMathlibExt
end
