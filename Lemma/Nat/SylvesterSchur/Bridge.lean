import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.Bridge
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[prime_dvd_choose_of_dvd_consecutive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
private lemma prime_dvd_choose_of_dvd_consecutive_eq
  {n k p j : ℕ}
-- given
  (hp : p.Prime)
  (hp_gt : n < p)
  (hj : j < n)
  (hdvd : p ∣ k + j) :
-- imply
  p ∣ Nat.choose (k + n - 1) n := by
-- proof
  apply Nat.SylvesterSchur.prime_dvd_choose_of_dvd_consecutive hp hp_gt hj hdvd

/--
[exists_dvd_consecutive_of_prime_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
private lemma exists_dvd_consecutive_of_prime_dvd_choose_eq
  {n k p : ℕ}
-- given
  (hp : p.Prime)
  (hp_dvd : p ∣ Nat.choose (k + n - 1) n) :
-- imply
  ∃ i < n, p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.exists_dvd_consecutive_of_prime_dvd_choose n k p hp hp_dvd

/--
[consecutive_of_exists_prime_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/Bridge.lean)
-/
@[path]
private lemma consecutive_of_exists_prime_dvd_choose_eq
  {n k : ℕ}
-- given
  (hbin : ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i := by
-- proof
  apply Nat.SylvesterSchur.consecutive_of_exists_prime_dvd_choose hbin


-- created on 2026-10-20
