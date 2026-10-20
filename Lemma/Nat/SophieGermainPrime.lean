import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SophieGermainPrime
open Nat


/--
[isSophieGermainPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
private lemma isSophieGermainPrime_iff_eq
  {p : ℕ} :
-- imply
  IsSophieGermainPrime p ↔ Nat.Prime p ∧ Nat.Prime (2 * p + 1) := by
-- proof
  apply Nat.isSophieGermainPrime_iff p

/--
[IsSophieGermainPrime.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
private lemma IsSophieGermainPrime_prime_eq
  {p : ℕ}
-- given
  (h : IsSophieGermainPrime p) :
-- imply
  Nat.Prime p := by
-- proof
  apply Nat.IsSophieGermainPrime.prime h

/--
[IsSophieGermainPrime.prime_two_mul_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SophieGermainPrime.lean)
-/
@[path]
private lemma IsSophieGermainPrime_prime_two_mul_add_one_eq
  {p : ℕ}
-- given
  (h : IsSophieGermainPrime p) :
-- imply
  Nat.Prime (2 * p + 1) := by
-- proof
  apply Nat.IsSophieGermainPrime.prime_two_mul_add_one h


-- created on 2026-10-20
