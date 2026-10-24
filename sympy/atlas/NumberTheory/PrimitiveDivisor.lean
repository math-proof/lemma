/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean -/

import Mathlib.Data.Nat.Prime.Defs

/-!
# Primitive divisors of integer sequences

For an integer-valued sequence `a`, a natural number `u ≥ 2` is a primitive divisor of
`a m` when it divides `a m` and no earlier positive-indexed term. A primitive prime divisor is
a primitive divisor that is prime.

## Main definitions

* `IntegerSequence.IsPrimitiveDivisor`
* `IntegerSequence.IsPrimitivePrimeDivisor`

## References

* M. Sadek, M. Wafik, and T. Yesin, *Arithmetic progressions in polynomial orbits*,
  [arXiv:2403.04397](https://arxiv.org/abs/2403.04397)
-/

namespace IntegerSequence

/-- `u` is a primitive divisor of the positive-indexed term `a m` of an integer sequence if
`u ≥ 2`, `u ∣ a m`, and `u` divides no `a s` with `1 ≤ s < m`. -/
def IsPrimitiveDivisor (a : ℕ → ℤ) (m u : ℕ) : Prop :=
  1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧ ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s

/-- A primitive prime divisor is a prime natural number that is a primitive divisor. -/
def IsPrimitivePrimeDivisor (a : ℕ → ℤ) (m u : ℕ) : Prop :=
  Nat.Prime u ∧ IsPrimitiveDivisor a m u
end IntegerSequence
