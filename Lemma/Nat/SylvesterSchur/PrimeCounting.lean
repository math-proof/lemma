import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.PrimeCounting
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le_eq
  {N r : ℕ}
-- given
  (hsmall : ¬ ∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_not_forall_prime_dvd_le hsmall

/--
[exists_large_prime_dvd_choose_of_upper_lt_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
private lemma exists_large_prime_dvd_choose_of_upper_lt_lower_eq
  {N r U : ℕ}
-- given
  (hupper : (∀ p : ℕ, p.Prime → p ∣ Nat.choose N r → p ≤ r) → Nat.choose N r ≤ U)
  (hbound : (U : ℚ) < ((N + 1 - r : ℕ) ^ r : ℚ) / (r ! : ℚ)) :
-- imply
  ∃ p : ℕ, p.Prime ∧ r < p ∧ p ∣ Nat.choose N r := by
-- proof
  apply Nat.SylvesterSchur.exists_large_prime_dvd_choose_of_upper_lt_lower hupper hbound

/--
[primeCounting_le_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
private lemma primeCounting_le_sub_one_eq
  {r : ℕ}
-- given
  (hr : 2 ≤ r) :
-- imply
  Nat.primeCounting r ≤ r - 1 := by
-- proof
  apply Nat.SylvesterSchur.primeCounting_le_sub_one hr

/--
[primeCounting_le_half_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
private lemma primeCounting_le_half_add_one_eq
  {r : ℕ} :
-- imply
  Nat.primeCounting r ≤ r / 2 + 1 := by
-- proof
  apply Nat.SylvesterSchur.primeCounting_le_half_add_one r

/--
[primeCounting_le_three_mul_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/PrimeCounting.lean)
-/
@[path]
private lemma primeCounting_le_three_mul_div_eight_eq
  {r : ℕ}
-- given
  (hr : 38 ≤ r) :
-- imply
  Nat.primeCounting r ≤ 3 * r / 8 := by
-- proof
  apply Nat.SylvesterSchur.primeCounting_le_three_mul_div_eight hr


-- created on 2026-10-20
