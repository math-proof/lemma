import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Def.Analysis.Polynomial.MultivariableMahlerMeasure.Part3
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

@[simp]
theorem torusEval_single_zero (θ : Fin n → ℝ) (c : ℂ) :
    torusEval θ (AddMonoidAlgebra.single 0 c) = c := by
  simp [torusEval]

@[simp]
theorem torusEval_single (θ : Fin n → ℝ) (c : ℂ) (e : Fin n → ℤ) :
    torusEval θ (AddMonoidAlgebra.single e c) = c * torusCharacter θ e := by
  rw [torusEval, AddMonoidAlgebra.lift_single (torusCharacterHom θ) e c]
  simp [torusCharacterHom, smul_eq_mul]

end MultivariableMahlerMeasure.MetaMathlibExt
end
