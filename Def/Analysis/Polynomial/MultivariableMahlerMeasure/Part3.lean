module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Theorem.Analysis.Polynomial.MultivariableMahlerMeasure.Part2

@[expose] public section

open Complex MeasureTheory Finset
open scoped Real


noncomputable section

namespace MultivariableMahlerMeasure.MetaMathlibExt

variable {n : ℕ}

/-- The multiplicative form of `torusCharacter`, used to evaluate a monoid algebra. -/
def torusCharacterHom (θ : Fin n → ℝ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun e := torusCharacter θ e.toAdd
  map_one' := by simp
  map_mul' a b := by
    have h : (a * b).toAdd = a.toAdd + b.toAdd := toAdd_mul a b
    simpa only [h] using torusCharacter_add θ a.toAdd b.toAdd

/-- Evaluation of a multivariable Laurent polynomial at a point of the unit torus. -/
noncomputable def torusEval (θ : Fin n → ℝ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) →ₐ[ℂ] ℂ :=
  (AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ)) (torusCharacterHom θ)

end MultivariableMahlerMeasure.MetaMathlibExt
end
