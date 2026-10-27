import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure.Part4
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-- `Fin 1 → ℤ` is additively equivalent to `ℤ`. -/
def finOneAddEquiv : (Fin 1 → ℤ) ≃+ ℤ :=
  AddEquiv.funUnique (Fin 1) ℤ

/-- The one-variable multivariable-Laurent representation agrees with Mathlib's
`LaurentPolynomial ℂ = AddMonoidAlgebra ℂ ℤ`. -/
noncomputable def bridgeLaurent :
    AddMonoidAlgebra ℂ (Fin 1 → ℤ) ≃ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.domCongr ℂ ℂ finOneAddEquiv

end MultivariableMahlerMeasure.MetaMathlibExt
end
