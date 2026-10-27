import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Def.Analysis.Polynomial.MultivariableMahlerMeasure.Part5
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

@[simp]
theorem bridgeLaurent_single (c : ℂ) (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) c) =
      AddMonoidAlgebra.single k c := by
  simp [bridgeLaurent, finOneAddEquiv]

@[simp]
theorem bridgeLaurent_C (c : ℂ) :
    bridgeLaurent (AddMonoidAlgebra.single (0 : Fin 1 → ℤ) c) = LaurentPolynomial.C c := by
  rw [show (0 : Fin 1 → ℤ) = fun _ => 0 from rfl, bridgeLaurent_single]
  rfl

@[simp]
theorem bridgeLaurent_T (k : ℤ) :
    bridgeLaurent (AddMonoidAlgebra.single (fun _ => k) 1) = LaurentPolynomial.T k := by
  rw [bridgeLaurent_single]
  rfl

@[simp]
theorem logarithmicMahlerMeasure_one {m : ℕ} :
    logarithmicMahlerMeasure (1 : AddMonoidAlgebra ℂ (Fin m → ℤ)) = 0 := by
  simp [logarithmicMahlerMeasure, normalizedBoxIntegral]

end MultivariableMahlerMeasure.MetaMathlibExt
end
