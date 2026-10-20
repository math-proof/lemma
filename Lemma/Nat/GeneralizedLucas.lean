import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedLucas
open Finset
open Nat


/--
[kGeneralizedLucas_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
private lemma kGeneralizedLucas_zero_eq
  {k : ℕ}
-- given
  (hk : 2 ≤ k)
  (h0 : 2 - (k : ℤ) ≤ 0) :
-- imply
  kGeneralizedLucas k hk 0 h0 = 2 := by
-- proof
  apply Nat.kGeneralizedLucas_zero k hk h0

/--
[kGeneralizedLucas_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
private lemma kGeneralizedLucas_one_eq
  {k : ℕ}
-- given
  (hk : 2 ≤ k)
  (h0 : 2 - (k : ℤ) ≤ 1) :
-- imply
  kGeneralizedLucas k hk 1 h0 = 1 := by
-- proof
  apply Nat.kGeneralizedLucas_one k hk h0

/--
[kGeneralizedLucas_neg_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
private lemma kGeneralizedLucas_neg_eq_zero_eq
  {k : ℕ}
  {n : ℤ}
-- given
  (hk : 3 ≤ k)
  (h : 2 - (k : ℤ) ≤ n)
  (hn : n ≤ -1) :
-- imply
  kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) n h = 0 := by
-- proof
  apply Nat.kGeneralizedLucas_neg_eq_zero k hk n h hn

/--
[kGeneralizedLucas_lower_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
private lemma kGeneralizedLucas_lower_zero_eq
  {k : ℕ}
-- given
  (hk : 3 ≤ k)
  (h : 2 - (k : ℤ) ≤ 2 - (k : ℤ)) :
-- imply
  kGeneralizedLucas k (Nat.le_trans (by decide : 2 ≤ 3) hk) (2 - (k : ℤ)) h =
    0 := by
-- proof
  apply Nat.kGeneralizedLucas_lower_zero k hk h

/--
[kGeneralizedLucas_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucas.lean)
-/
@[path]
private lemma kGeneralizedLucas_recurrence_eq
  {k : ℕ}
  {n : ℤ}
-- given
  (hk : 2 ≤ k)
  (hn : 2 ≤ n)
  (h : 2 - (k : ℤ) ≤ n) :
-- imply
  kGeneralizedLucas k hk n h =
    ∑ i : Fin k,
    kGeneralizedLucas k hk ((n - (k : ℤ)) + (i.val : ℤ)) (by omega) := by
-- proof
  apply Nat.kGeneralizedLucas_recurrence k hk n hn h


-- created on 2026-10-20
