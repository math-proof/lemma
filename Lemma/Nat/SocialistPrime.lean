import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SocialistPrime
open Nat


/--
[IsSocialistPrime.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
private lemma IsSocialistPrime_prime_eq
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  Nat.Prime p := by
-- proof
  apply Nat.IsSocialistPrime.prime h

/--
[IsSocialistPrime.five_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
private lemma IsSocialistPrime_five_lt_eq
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  5 < p := by
-- proof
  apply Nat.IsSocialistPrime.five_lt h

/--
[IsSocialistPrime.pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
private lemma IsSocialistPrime_pairwise_eq
  {p : ℕ}
-- given
  (h : IsSocialistPrime p) :
-- imply
  Set.Pairwise (Set.Icc 2 (p - 1)) (fun k l => k.factorial % p ≠ l.factorial % p) := by
-- proof
  apply Nat.IsSocialistPrime.pairwise h

/--
[IsSocialistPrime.factorial_mod_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SocialistPrime.lean)
-/
@[path]
private lemma IsSocialistPrime_factorial_mod_ne_eq
  {p : ℕ}
  {a b : ℕ}
-- given
  (h : IsSocialistPrime p)
  (ha : a ∈ Set.Icc 2 (p - 1))
  (hb : b ∈ Set.Icc 2 (p - 1))
  (hab : a ≠ b) :
-- imply
  a.factorial % p ≠ b.factorial % p := by
-- proof
  apply Nat.IsSocialistPrime.factorial_mod_ne h ha hb hab


-- created on 2026-10-20
