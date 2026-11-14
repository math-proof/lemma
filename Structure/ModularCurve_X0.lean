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

def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

end QExpand

section RatAlgebra

variable (N : ℕ) [NeZero N]


end RatAlgebra

section JFunction

def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3

def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))

def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24

def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1

def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv

def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)

def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ

end JFunction

def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq


section NamedInputs

def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]

def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

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
