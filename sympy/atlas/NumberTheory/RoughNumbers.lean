/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean -/

import Mathlib.NumberTheory.SmoothNumbers

/-!
# Rough natural numbers

This file defines the source-faithful notion of `z`-rough natural number used in
Mayank Pandey, *Numbers with at most 2 prime factors in short arithmetic
progressions* (arXiv `2307.14890v1`): footnote on line 91 of `hybrid.tex` says
that by a `z`-rough number, one means a number with no prime factors `≤ z`.

The candidate number and the roughness bound are both natural numbers. Zero is
not rough. The unit `1` is rough for every bound by vacuity; this agrees with
Fred B. Holt, *On the counts of p-rough numbers* (arXiv `2308.07570`), which
explicitly includes `1` as a `p`-rough number.

Mathlib's `Nat.roughNumbersUpTo N k` is only the positive complement of
`k`-smoothness below `N` (a number with at least one prime factor `≥ k`); it is
not the source predicate, which demands that *every* prime factor exceed the
bound. We bridge to it below without conflating the two notions.
-/

namespace Nat

/-- A natural number `n` is `k`-rough if it is positive and has no prime factor
at most `k`: every natural prime divisor `p` of `n` satisfies `k < p`.
This is the footnote definition of Pandey (`2307.14890v1`, `hybrid.tex` line 91).
Zero is not rough; `1` is rough for every bound by vacuity. -/
def IsRough (n k : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p

/-- Equivalent finite characterization through the prime-factor list. -/
theorem isRough_iff_primeFactorsList {n k : ℕ} :
    n.IsRough k ↔ n ≠ 0 ∧ ∀ p ∈ primeFactorsList n, k < p := by
  constructor
  · intro h
    refine ⟨h.ne_zero, fun p hp => ?_⟩
    exact h.lt_of_prime_dvd (prime_of_mem_primeFactorsList hp)
      (dvd_of_mem_primeFactorsList hp)
  · intro h
    refine ⟨h.1, fun p hp hdvd => ?_⟩
    exact h.2 p ((mem_primeFactorsList h.1).mpr ⟨hp, hdvd⟩)

/-- Roughness is decidable via the finite prime-factor characterization. -/
instance decidableIsRough (n k : ℕ) : Decidable (n.IsRough k) :=
  decidable_of_iff _ (isRough_iff_primeFactorsList (n := n) (k := k)).symm
end Nat
