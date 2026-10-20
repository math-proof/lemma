/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean -/

import Mathlib.Data.Nat.Squarefree

/-!
# Power-free natural numbers

This file formalizes the classical notion of `k`-free natural number from
Dietmann–Marmon, *The density of twins of k-free numbers* (arXiv `1307.2481v2`):
for `k ≥ 2`, a positive integer is `k`-free when it is not divisible by the
`k`-th power of any prime.

We prove that divisors of a power-free number are power-free at the same level,
monotonicity in the exponent, and that `2`-free is exactly squarefree.
-/

namespace Nat

/-- A natural number `n` is `k`-free if `2 ≤ k`, `0 < n`, and no prime
`k`-th power divides `n`. -/
def IsPowerFree (n k : ℕ) : Prop :=
  2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n

/-- Transparent characterization of `IsPowerFree`. -/
theorem isPowerFree_iff {n k : ℕ} :
    n.IsPowerFree k ↔ 2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n :=
  Iff.rfl

/-- The exponent restriction of a power-free number. -/
theorem IsPowerFree.two_le {n k : ℕ} (h : n.IsPowerFree k) : 2 ≤ k :=
  h.1

/-- Positivity of a power-free number. -/
theorem IsPowerFree.pos {n k : ℕ} (h : n.IsPowerFree k) : 0 < n :=
  h.2.1

/-- The prime-power exclusion of a power-free number. -/
theorem IsPowerFree.not_dvd {n k p : ℕ} (h : n.IsPowerFree k)
    (hp : p.Prime) : ¬p ^ k ∣ n :=
  h.2.2 p hp

/-- Divisors of a power-free number are power-free at the same level. -/
theorem IsPowerFree.of_dvd {m n k : ℕ} (h : n.IsPowerFree k)
    (hmn : m ∣ n) : m.IsPowerFree k :=
  ⟨h.two_le, Nat.pos_of_dvd_of_pos hmn h.pos,
    fun _ hp hdiv => h.not_dvd hp (hdiv.trans hmn)⟩

/-- Monotonicity in the exponent: `k`-free implies `l`-free for `k ≤ l`. -/
theorem IsPowerFree.mono {n k l : ℕ} (h : n.IsPowerFree k)
    (hkl : k ≤ l) : n.IsPowerFree l := by
  refine ⟨le_trans h.two_le hkl, h.pos, fun p hp hdiv => ?_⟩
  have hpk : p ^ k ∣ p ^ l := by
    obtain ⟨d, rfl⟩ := Nat.le.dest hkl
    rw [pow_add]
    exact dvd_mul_right _ _
  exact h.not_dvd hp (hpk.trans hdiv)

/-- `2`-free is exactly squarefree, via `Nat.squarefree_iff_prime_squarefree`. -/
theorem isPowerFree_two {n : ℕ} : n.IsPowerFree 2 ↔ Squarefree n := by
  constructor
  · intro h
    rw [squarefree_iff_prime_squarefree]
    intro x hx hdiv
    exact h.not_dvd hx (by rwa [pow_two])
  · intro h
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [squarefree_iff_prime_squarefree] at h
      exact h 2 prime_two (dvd_zero _)
    refine ⟨le_refl 2, Nat.pos_of_ne_zero hn0, fun p hp hdiv => ?_⟩
    rw [squarefree_iff_prime_squarefree] at h
    exact h p hp (by rw [← pow_two]; exact hdiv)

end Nat
