module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure.Part4

@[expose] public section

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
