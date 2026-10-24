/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CarmichaelNumber.lean -/

import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.RingTheory.ZMod

/-!
# Korselt's criterion

This file formalizes Korselt's criterion for Carmichael numbers.

A positive composite integer `n` is a Carmichael number if `a ^ n ≡ a [MOD n]`
for every `a : ℕ`, equivalently `∀ x : ZMod n, x ^ n = x`. By
`ZMod.natCast_zmod_val` the `ℕ`-quantified condition is equivalent to the
statement for all integers. We prove that `n` is Carmichael iff `n` is
squarefree and for every prime divisor `p ∣ n`, `p - 1 ∣ n - 1`. The proof uses
the Carmichael function `ArithmeticFunction.carmichael` as the exponent of
`(ZMod n)ˣ` to bridge the universal property and the divisibility condition.

References:

* A. Korselt, *Problème chinois*, 1899.
* T. Wright, *`(a, a)`-Carmichael numbers and greatest common divisors of `p - a`*,
  [arXiv:2607.02738v1](https://arxiv.org/abs/2607.02738v1), lines 95–103.
-/

/-- A composite natural number satisfying Fermat's congruence for every base. -/
def Nat.IsCarmichaelNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n]
