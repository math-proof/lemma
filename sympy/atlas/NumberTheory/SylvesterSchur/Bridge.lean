/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean -/

/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Sylvester-Schur: binomial and consecutive forms

This file records the elementary bridge between the binomial-coefficient form

`∃ p, p.Prime ∧ i < p ∧ p ∣ Nat.choose N i`, for `1 ≤ i` and `2 * i ≤ N`,

and the consecutive-integer form

among `n` consecutive integers starting at `k` with `n < k`, one has a prime divisor
greater than `n`.

The bridge contains no use of the main Sylvester-Schur theorem itself.
-/

namespace Nat.SylvesterSchur

open scoped BigOperators

open Finset Nat

/-- If a prime `n < p` divides one term in the `n`-term block starting at `k`, then it
divides the corresponding binomial coefficient. -/
theorem prime_dvd_choose_of_dvd_consecutive {n k p j : ℕ} (hp : p.Prime) (hp_gt : n < p)
    (hj : j < n) (hdvd : p ∣ k + j) :
    p ∣ Nat.choose (k + n - 1) n := by
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) :=
    hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hj))
  rw [← hprod_eq_range, hprod_eq] at hp_dvd_prod
  exact (hp.coprime_factorial_of_lt hp_gt).dvd_of_dvd_mul_left hp_dvd_prod

/-- If a prime `n < p` divides `Nat.choose (k+n-1) n`, then it divides some term
`k+i` in the corresponding `n`-term block. -/
theorem exists_dvd_consecutive_of_prime_dvd_choose (n k p : ℕ) (hp : p.Prime)
    (hp_dvd : p ∣ Nat.choose (k + n - 1) n) :
    ∃ i < n, p ∣ k + i := by
  have hprod_eq : k.ascFactorial n = n ! * Nat.choose (k + n - 1) n :=
    Nat.ascFactorial_eq_factorial_mul_choose' k n
  have hprod_eq_range : k.ascFactorial n = ∏ i ∈ Finset.range n, (k + i) :=
    Nat.ascFactorial_eq_prod_range k n
  have hp_dvd_prod : p ∣ ∏ i ∈ Finset.range n, (k + i) := by
    rw [← hprod_eq_range, hprod_eq]
    exact dvd_mul_of_dvd_right hp_dvd (n !)
  rw [hp.prime.dvd_finsetProd_iff] at hp_dvd_prod
  simpa [Finset.mem_range] using hp_dvd_prod

/-- A large prime divisor of the relevant binomial coefficient gives a large prime divisor in
the consecutive block. -/
theorem consecutive_of_exists_prime_dvd_choose {n k : ℕ}
    (hbin : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
    ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
  obtain ⟨p, hp, hp_gt, hp_dvd⟩ := hbin
  obtain ⟨i, hi, hi_dvd⟩ :=
    exists_dvd_consecutive_of_prime_dvd_choose n k p hp hp_dvd
  exact ⟨i, hi, p, hp, hp_gt, hi_dvd⟩

end Nat.SylvesterSchur
