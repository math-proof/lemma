/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.HasLawExists

/-!
# Rademacher random multiplicative functions

This file constructs the classical Rademacher random multiplicative function. Independent
uniform signs are assigned to the primes, extended multiplicatively to squarefree natural
numbers, and set to zero on nonsquarefree inputs.

The arithmetic function is represented by

`μ(n)² ∏_{p ∣ n} Xₚ`,

using pointwise multiplication of arithmetic functions, not Dirichlet convolution. The module
provides the probability law, existence of an independent prime-indexed family, measurability of
the resulting evaluations, and the basic squarefree and multiplicative identities.

## References

* [B. Durkan and A. Pearce-Crump, *A sharp almost sure upper bound for partial sums of random
  multiplicative functions*][durkan2026]
* [R. Zhu and T. Zhang, *Better than square-root cancellation in Piatetski-Shapiro
  sequences*][zhu2026]
* [W. Verreault, *Almost sure upper bound for sums of random multiplicative functions and
  critical chaos*][verreault2026]

[durkan2026]: https://arxiv.org/abs/2607.29429
[zhu2026]: https://arxiv.org/abs/2608.15807
[verreault2026]: https://arxiv.org/abs/2608.21354
-/

open MeasureTheory ProbabilityTheory ArithmeticFunction
open scoped ENNReal

namespace MetaMathlibExt.RandomMultiplicativeFunction

/-- The uniform probability measure on the two integer units `{-1, 1}`. -/
noncomputable def rademacherMeasure : Measure ℤˣ :=
  (PMF.uniformOfFintype ℤˣ).toMeasure

noncomputable instance instIsProbabilityMeasureRademacherMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- A measurable independent family of random variables, indexed by primes, each with the
uniform law on the integer units. -/
def IsRademacherFamily {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Nat.Primes → Ω → ℤˣ) : Prop :=
  (∀ p, Measurable (X p)) ∧ (∀ p, HasLaw (X p) rademacherMeasure μ) ∧ iIndepFun X μ

/-- The sign assigned by `X` to a prime natural number, and the neutral value `1` on nonprimes. -/
def primeSignNat {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (n : ℕ) (ω : Ω) : ℤ :=
  if h : Nat.Prime n then (X ⟨n, h⟩ ω : ℤ) else 1

/-- The Rademacher random multiplicative function associated with a realization of the prime
signs. It is the pointwise product of the square of the Möbius function and the product of the
signs over the prime divisors. -/
noncomputable def rademacherFunction {Ω : Type*} (X : Nat.Primes → Ω → ℤˣ) (ω : Ω) :
    ArithmeticFunction ℤ :=
  (moebius.pmul moebius).pmul (prodPrimeFactors fun p => primeSignNat X p ω)
end MetaMathlibExt.RandomMultiplicativeFunction
