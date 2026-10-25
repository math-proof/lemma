/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.HasLawExists
open MeasureTheory ProbabilityTheory ArithmeticFunction
open scoped ENNReal

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


namespace MetaMathlibExt.RandomMultiplicativeFunction

/-- The uniform probability measure on the two integer units `{-1, 1}`. -/
noncomputable def rademacherMeasure : Measure ℤˣ :=
  (PMF.uniformOfFintype ℤˣ).toMeasure

end MetaMathlibExt.RandomMultiplicativeFunction
