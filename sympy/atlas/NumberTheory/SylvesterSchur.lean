/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur.lean -/

/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Basic

import sympy.atlas.NumberTheory.SylvesterSchur.Bridge
import sympy.atlas.NumberTheory.SylvesterSchur.ErdosKey
/-!
# Sylvester-Schur theorem

This file exposes the `Nat.ascFactorial` form of the Sylvester-Schur theorem.

## Main statements

* `Nat.exists_prime_gt_and_dvd_ascFactorial`: among `k` consecutive natural numbers
  starting at `n`, where `0 < k < n`, one term has a prime divisor greater than `k`.

## References

The proof follows [Erdős, *A theorem of Sylvester and Schur*, J. London Math. Soc. 9
(1934), 282–288](https://doi.org/10.1112/jlms/s1-9.4.282).

## Tags

Sylvester-Schur theorem, prime divisors, binomial coefficients, ascending factorials
-/

namespace Nat

open SylvesterSchur

/-- Sylvester-Schur theorem in Mathlib's `Nat.ascFactorial` API form. -/
theorem exists_prime_gt_and_dvd_ascFactorial {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ n.ascFactorial k := by
  obtain ⟨p, hp_prime, hp_gt, hp_dvd⟩ :=
    SylvesterSchur.Internal.erdos_choose_prime_factor_gt k hk n hkn
  obtain ⟨i, hi_lt, hi_dvd⟩ :=
    SylvesterSchur.exists_dvd_consecutive_of_prime_dvd_choose k n p hp_prime hp_dvd
  refine ⟨p, hp_prime, hp_gt, ?_⟩
  rw [Nat.ascFactorial_eq_prod_range]
  exact hi_dvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi_lt))

end Nat
