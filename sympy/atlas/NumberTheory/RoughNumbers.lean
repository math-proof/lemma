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

/-- Transparent characterization of roughness. -/
theorem isRough_iff {n k : ℕ} :
    n.IsRough k ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p :=
  Iff.rfl

/-- A rough number is nonzero. -/
theorem IsRough.ne_zero {n k : ℕ} (h : n.IsRough k) : n ≠ 0 :=
  h.1

/-- A rough number is positive. -/
theorem IsRough.pos {n k : ℕ} (h : n.IsRough k) : 0 < n :=
  Nat.pos_of_ne_zero h.ne_zero

/-- Prime-divisor lower-bound projection: every prime divisor of a `k`-rough
number exceeds `k`. -/
theorem IsRough.lt_of_prime_dvd {n k p : ℕ} (h : n.IsRough k) (hp : p.Prime)
    (hdvd : p ∣ n) : k < p :=
  h.2 p hp hdvd

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

/-- The unit `1` is rough for every bound by vacuity. -/
theorem isRough_one (k : ℕ) : (1 : ℕ).IsRough k :=
  ⟨one_ne_zero, fun _ hp hdvd => (hp.ne_one (Nat.dvd_one.mp hdvd)).elim⟩

/-- A prime `p` is `k`-rough exactly when `k < p`. -/
theorem Prime.isRough_iff {p k : ℕ} (hp : p.Prime) : p.IsRough k ↔ k < p := by
  constructor
  · intro h
    exact h.lt_of_prime_dvd hp dvd_rfl
  · intro hk
    refine ⟨hp.ne_zero, fun q hq hdvd => ?_⟩
    have heq : q = p := (prime_dvd_prime_iff_eq hq hp).mp hdvd
    rw [heq]
    exact hk

/-- Positive divisors of a rough number are rough. -/
theorem IsRough.of_dvd {m d k : ℕ} (h : m.IsRough k) (hdvd : d ∣ m) (hd : d ≠ 0) :
    d.IsRough k :=
  ⟨hd, fun _ hp hpd => h.lt_of_prime_dvd hp (hpd.trans hdvd)⟩

/-- Multiplication closure as an if-and-only-if: a product is `k`-rough exactly
when both factors are. -/
theorem isRough_mul {m n k : ℕ} : (m * n).IsRough k ↔ m.IsRough k ∧ n.IsRough k := by
  constructor
  · intro h
    refine ⟨h.of_dvd (Nat.dvd_mul_right m n) ?_,
      h.of_dvd (Nat.dvd_mul_left n m) ?_⟩
    · intro hm
      exact h.ne_zero (by rw [hm, zero_mul])
    · intro hn
      exact h.ne_zero (by rw [hn, mul_zero])
  · rintro ⟨hm, hn⟩
    refine ⟨mul_ne_zero hm.ne_zero hn.ne_zero, fun _ hp hdvd => ?_⟩
    rw [hp.dvd_mul] at hdvd
    exact hdvd.elim (hm.lt_of_prime_dvd hp) (hn.lt_of_prime_dvd hp)

/-- Multiplication closure, forward direction. -/
theorem IsRough.mul {m n k : ℕ} (hm : m.IsRough k) (hn : n.IsRough k) :
    (m * n).IsRough k :=
  isRough_mul.mpr ⟨hm, hn⟩

/-- Antitonicity in the bound: a `k`-rough number is `l`-rough for `l ≤ k`. -/
theorem IsRough.of_le {n k l : ℕ} (h : n.IsRough k) (hle : l ≤ k) : n.IsRough l :=
  ⟨h.ne_zero, fun _ hp hdvd => lt_of_le_of_lt hle (h.lt_of_prime_dvd hp hdvd)⟩

/-- Bridge to `Nat.smoothNumbers` under Mathlib's strict-bound convention:
a number that is both `k`-rough and `(k + 1)`-smooth must equal `1`. -/
theorem IsRough.eq_one_of_mem_smoothNumbers {n k : ℕ}
    (hrough : n.IsRough k) (hsmooth : n ∈ smoothNumbers (k + 1)) : n = 1 := by
  by_contra hn1
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
  have hlt1 : k < p := hrough.lt_of_prime_dvd hp hpdvd
  rw [Nat.mem_smoothNumbers] at hsmooth
  have hmem : p ∈ Nat.primeFactorsList n :=
    (Nat.mem_primeFactorsList hrough.ne_zero).mpr ⟨hp, hpdvd⟩
  have hlt2 : p < k + 1 := hsmooth.2 p hmem
  omega

/-- Bridge of nonunit source-rough numbers bounded by `N` into Mathlib's
`Nat.roughNumbersUpTo N (k + 1)`. Note that the latter is only the positive
complement of `(k + 1)`-smoothness (some prime factor is `≥ k + 1`), not the
source predicate (every prime factor exceeds `k`). -/
theorem IsRough.mem_roughNumbersUpTo {n N k : ℕ}
    (h : n.IsRough k) (hle : n ≤ N) (hn1 : n ≠ 1) :
    n ∈ roughNumbersUpTo N (k + 1) := by
  rw [roughNumbersUpTo, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, h.ne_zero, ?_⟩
  intro hsmooth
  exact hn1 (h.eq_one_of_mem_smoothNumbers hsmooth)

end Nat
