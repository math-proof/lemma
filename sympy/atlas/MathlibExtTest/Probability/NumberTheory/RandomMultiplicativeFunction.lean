/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/NumberTheory/RandomMultiplicativeFunction.lean -/


import sympy.atlas.Probability.NumberTheory.RandomMultiplicativeFunction
import Lemma.Measure.NumberTheory.RandomMultiplicativeFunction

import Mathlib.Tactic.NormNum


open MeasureTheory ProbabilityTheory ArithmeticFunction
open MetaMathlibExt.RandomMultiplicativeFunction

example (x : ℤˣ) : rademacherMeasure {x} = (2 : ENNReal)⁻¹ :=
  rademacherMeasure_singleton x

example :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : Nat.Primes → Ω → ℤˣ),
      IsRademacherFamily μ X ∧ IsProbabilityMeasure μ :=
  exists_rademacherFamily

example {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    primeSignNat X 4 ω = 1 := by
  exact primeSignNat_not_prime (by decide)

example {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    rademacherFunction X ω 6 = primeSignNat X 2 ω * primeSignNat X 3 ω := by
  calc
    rademacherFunction X ω 6 = rademacherFunction X ω (2 * 3) := by norm_num
    _ = rademacherFunction X ω 2 * rademacherFunction X ω 3 :=
      isMultiplicative_rademacherFunction.map_mul_of_coprime (by decide)
    _ = primeSignNat X 2 ω * primeSignNat X 3 ω := by
      rw [rademacherFunction_prime (by decide), rademacherFunction_prime (by decide)]

example {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    rademacherFunction X ω 0 = 0 := by simp

example {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    rademacherFunction X ω 12 = 0 := by
  apply rademacherFunction_eq_zero_of_not_squarefree
  decide

example {Ω : Type*} {X : Nat.Primes → Ω → ℤˣ} {ω : Ω} :
    rademacherFunction X ω 9 = 0 := by
  have h : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h]
  exact rademacherFunction_prime_sq (by decide)

example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Nat.Primes → Ω → ℤˣ}
    (hX : IsRademacherFamily μ X) (n : ℕ) :
    Measurable (fun ω => rademacherFunction X ω n) :=
  hX.measurable_rademacherFunction n
