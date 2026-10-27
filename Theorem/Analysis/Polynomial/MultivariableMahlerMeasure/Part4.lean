import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Def.Analysis.Polynomial.MultivariableMahlerMeasure.Part4
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

@[simp]
theorem logarithmicMahlerMeasure_const {m : ℕ} (c : ℂ) :
    logarithmicMahlerMeasure
      (AddMonoidAlgebra.single (0 : Fin m → ℤ) c) = Real.log ‖c‖ := by
  simp only [logarithmicMahlerMeasure, torusEval_single_zero, normalizedBoxIntegral,
    integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ, Measure.real]
  rw [Real.volume_Icc_pi_toReal (fun _ => by positivity)]
  simp [Finset.prod_const, Real.pi_ne_zero]

@[simp]
theorem logarithmicMahlerMeasure_zero {m : ℕ} :
    logarithmicMahlerMeasure (0 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

end MultivariableMahlerMeasure.MetaMathlibExt
end
