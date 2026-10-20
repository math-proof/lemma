import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.KFull
open Nat


/--
[powerfulPart_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_zero_eq
  :
-- imply
  powerfulPart 0 = 1 := by
-- proof
  apply Nat.powerfulPart_zero

/--
[powerfulPart_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_one_eq
  :
-- imply
  powerfulPart 1 = 1 := by
-- proof
  apply Nat.powerfulPart_one

/--
[powerfulPart_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_factorization_eq
  {n p : ℕ} :
-- imply
  (powerfulPart n).factorization p =
    if 2 ≤ n.factorization p then n.factorization p else 0 := by
-- proof
  apply Nat.powerfulPart_factorization n p

/--
[powerfulPart_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_dvd_eq
  {n : ℕ} :
-- imply
  powerfulPart n ∣ n := by
-- proof
  apply Nat.powerfulPart_dvd n

/--
[isKFull_iff_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_iff_factorization_eq
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  IsKFull k n ↔ ∀ p : ℕ, p.Prime → p ∣ n → k ≤ n.factorization p := by
-- proof
  apply Nat.isKFull_iff_factorization hn

/--
[not_isKFull_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma not_isKFull_zero_eq
  {k : ℕ} :
-- imply
  ¬ IsKFull k 0 := by
-- proof
  apply Nat.not_isKFull_zero k

/--
[isKFull_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_one_eq
  {k : ℕ} :
-- imply
  IsKFull k 1 := by
-- proof
  apply Nat.isKFull_one k

/--
[isKFull_k_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_k_eq_zero_eq
  {n : ℕ} :
-- imply
  IsKFull 0 n ↔ n ≠ 0 := by
-- proof
  apply Nat.isKFull_k_eq_zero

/--
[isKFull_k_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_k_eq_one_eq
  {n : ℕ} :
-- imply
  IsKFull 1 n ↔ n ≠ 0 := by
-- proof
  apply Nat.isKFull_k_eq_one

/--
[isKFull_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_mono_eq
  {j k n : ℕ}
-- given
  (hjk : j ≤ k)
  (h : IsKFull k n) :
-- imply
  IsKFull j n := by
-- proof
  apply Nat.isKFull_mono hjk h

/--
[isKFull_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_of_two_le_eq
  {k n : ℕ}
-- given
  (hk : 2 ≤ k)
  (h : IsKFull k n) :
-- imply
  IsKFull 2 n := by
-- proof
  apply Nat.isKFull_of_two_le hk h

/--
[isKFull_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma isKFull_two_eq
  {n : ℕ} :
-- imply
  IsKFull 2 n ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n := by
-- proof
  apply Nat.isKFull_two


-- created on 2026-10-20
