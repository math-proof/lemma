import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RoughNumbers
open Nat


/--
[isRough_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma isRough_iff_eq
  {n k : ℕ} :
-- imply
  n.IsRough k ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → k < p := by
-- proof
  apply Nat.isRough_iff

/--
[IsRough.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_ne_zero_eq
  {n k : ℕ}
-- given
  (h : n.IsRough k) :
-- imply
  n ≠ 0 := by
-- proof
  apply Nat.IsRough.ne_zero h

/--
[IsRough.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_pos_eq
  {n k : ℕ}
-- given
  (h : n.IsRough k) :
-- imply
  0 < n := by
-- proof
  apply Nat.IsRough.pos h

/--
[IsRough.lt_of_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_lt_of_prime_dvd_eq
  {n k p : ℕ}
-- given
  (h : n.IsRough k)
  (hp : p.Prime)
  (hdvd : p ∣ n) :
-- imply
  k < p := by
-- proof
  apply Nat.IsRough.lt_of_prime_dvd h hp hdvd

/--
[isRough_iff_primeFactorsList](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma isRough_iff_primeFactorsList_eq
  {n k : ℕ} :
-- imply
  n.IsRough k ↔ n ≠ 0 ∧ ∀ p ∈ primeFactorsList n, k < p := by
-- proof
  apply Nat.isRough_iff_primeFactorsList

/--
[isRough_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma isRough_one_eq
  {k : ℕ} :
-- imply
  (1 : ℕ).IsRough k := by
-- proof
  apply Nat.isRough_one k

/--
[Prime.isRough_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma Prime_isRough_iff_eq
  {p k : ℕ}
-- given
  (hp : p.Prime) :
-- imply
  p.IsRough k ↔ k < p := by
-- proof
  apply Nat.Prime.isRough_iff hp

/--
[IsRough.of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_of_dvd_eq
  {m d k : ℕ}
-- given
  (h : m.IsRough k)
  (hdvd : d ∣ m)
  (hd : d ≠ 0) :
-- imply
  d.IsRough k := by
-- proof
  apply Nat.IsRough.of_dvd h hdvd hd

/--
[isRough_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma isRough_mul_eq
  {m n k : ℕ} :
-- imply
  (m * n).IsRough k ↔ m.IsRough k ∧ n.IsRough k := by
-- proof
  apply Nat.isRough_mul

/--
[IsRough.mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_mul_eq
  {m n k : ℕ}
-- given
  (hm : m.IsRough k)
  (hn : n.IsRough k) :
-- imply
  (m * n).IsRough k := by
-- proof
  apply Nat.IsRough.mul hm hn

/--
[IsRough.of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_of_le_eq
  {n k l : ℕ}
-- given
  (h : n.IsRough k)
  (hle : l ≤ k) :
-- imply
  n.IsRough l := by
-- proof
  apply Nat.IsRough.of_le h hle

/--
[IsRough.eq_one_of_mem_smoothNumbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_eq_one_of_mem_smoothNumbers_eq
  {n k : ℕ}
-- given
  (hrough : n.IsRough k)
  (hsmooth : n ∈ smoothNumbers (k + 1)) :
-- imply
  n = 1 := by
-- proof
  apply Nat.IsRough.eq_one_of_mem_smoothNumbers hrough hsmooth

/--
[IsRough.mem_roughNumbersUpTo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RoughNumbers.lean)
-/
@[path]
private lemma IsRough_mem_roughNumbersUpTo_eq
  {n N k : ℕ}
-- given
  (h : n.IsRough k)
  (hle : n ≤ N)
  (hn1 : n ≠ 1) :
-- imply
  n ∈ roughNumbersUpTo N (k + 1) := by
-- proof
  apply Nat.IsRough.mem_roughNumbersUpTo h hle hn1


-- created on 2026-10-20
