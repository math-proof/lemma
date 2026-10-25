import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section QExpand

variable {R : Type*} [CommRing R]

variable (R) in


variable (N : ℕ) [NeZero N]


end QExpand

section RatAlgebra

variable (N : ℕ) [NeZero N]


end RatAlgebra

section JFunction


end JFunction


section NamedInputs

def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]

def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp]

structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where

  Φ : Polynomial (Polynomial ℤ)

  monic : Φ.Monic

  natDegree_eq : Φ.natDegree = dedekindPsi N

  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0


end NamedInputs

section FunctionField

variable (N : ℕ) [NeZero N]


end FunctionField


namespace ModularPolynomialData

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)


end ModularPolynomialData

section AllDivisors

variable (N : ℕ) [NeZero N]


end AllDivisors

end ModularCurve
