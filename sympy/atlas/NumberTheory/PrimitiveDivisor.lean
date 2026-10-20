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

theorem IsPrimitiveDivisor.one_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : 1 ≤ m :=
  h.1

theorem IsPrimitiveDivisor.two_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : 2 ≤ u :=
  h.2.1

theorem IsPrimitiveDivisor.dvd {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) : (u : ℤ) ∣ a m :=
  h.2.2.1

theorem IsPrimitiveDivisor.not_dvd_of_lt {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitiveDivisor a m u) {s : ℕ} (hs : 1 ≤ s) (hsm : s < m) :
    ¬ (u : ℤ) ∣ a s :=
  h.2.2.2 s hs hsm

theorem IsPrimitivePrimeDivisor.prime {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : Nat.Prime u :=
  h.1

theorem IsPrimitivePrimeDivisor.toIsPrimitiveDivisor {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : IsPrimitiveDivisor a m u :=
  h.2

theorem IsPrimitivePrimeDivisor.one_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : 1 ≤ m :=
  h.toIsPrimitiveDivisor.one_le

theorem IsPrimitivePrimeDivisor.two_le {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : 2 ≤ u :=
  h.toIsPrimitiveDivisor.two_le

theorem IsPrimitivePrimeDivisor.dvd {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) : (u : ℤ) ∣ a m :=
  h.toIsPrimitiveDivisor.dvd

theorem IsPrimitivePrimeDivisor.not_dvd_of_lt {a : ℕ → ℤ} {m u : ℕ}
    (h : IsPrimitivePrimeDivisor a m u) {s : ℕ} (hs : 1 ≤ s) (hsm : s < m) :
    ¬ (u : ℤ) ∣ a s :=
  h.toIsPrimitiveDivisor.not_dvd_of_lt hs hsm

@[simp]
theorem isPrimitivePrimeDivisor_iff {a : ℕ → ℤ} {m u : ℕ} :
    IsPrimitivePrimeDivisor a m u ↔
      Nat.Prime u ∧ 1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧
        ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s :=
  Iff.rfl

/-- The index where a primitive divisor occurs is no larger than any positive index where that
divisor occurs. -/
theorem IsPrimitiveDivisor.le_of_dvd {a : ℕ → ℤ} {m u n : ℕ}
    (hm : IsPrimitiveDivisor a m u) (hn : 1 ≤ n) (hdvd : (u : ℤ) ∣ a n) :
    m ≤ n := by
  by_contra hmn
  exact hm.not_dvd_of_lt hn (by omega) hdvd

/-- A fixed divisor can be primitive at only one index of a sequence. -/
theorem IsPrimitiveDivisor.unique {a : ℕ → ℤ} {m n u : ℕ}
    (hm : IsPrimitiveDivisor a m u) (hn : IsPrimitiveDivisor a n u) :
    m = n :=
  le_antisymm (hm.le_of_dvd hn.one_le hn.dvd) (hn.le_of_dvd hm.one_le hm.dvd)

/-- A fixed prime divisor can be primitive at only one index of a sequence. -/
theorem IsPrimitivePrimeDivisor.unique {a : ℕ → ℤ} {m n u : ℕ}
    (hm : IsPrimitivePrimeDivisor a m u) (hn : IsPrimitivePrimeDivisor a n u) :
    m = n :=
  hm.toIsPrimitiveDivisor.unique hn.toIsPrimitiveDivisor

end IntegerSequence
