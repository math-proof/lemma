import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure.Part3
open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-- The normalized integral of `f` over the box `[0, 2π]ⁿ`. -/
noncomputable def normalizedBoxIntegral {m : ℕ} (f : (Fin m → ℝ) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ m)⁻¹ *
    ∫ x in Set.Icc (0 : Fin m → ℝ) (fun _ => 2 * Real.pi), f x ∂volume

/-- The multivariable logarithmic Mahler measure of a complex Laurent polynomial.

The cited source applies this formula to nonzero polynomials. Following Mathlib's
`Polynomial.logMahlerMeasure`, the Lean definition is total; in particular, its value at zero is
zero under `Real.log_zero` and the convention for the Bochner integral.
-/
noncomputable def logarithmicMahlerMeasure {m : ℕ}
    (F : AddMonoidAlgebra ℂ (Fin m → ℤ)) : ℝ :=
  normalizedBoxIntegral fun θ => Real.log ‖torusEval θ F‖

end MultivariableMahlerMeasure.MetaMathlibExt
end
