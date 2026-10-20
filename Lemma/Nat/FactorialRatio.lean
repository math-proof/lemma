import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FactorialRatio


/--
[factorialProd_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma factorialProd_nil_eq
  {n : ℕ} :
-- imply
  factorialProd [] n = 1 := by
-- proof
  apply factorialProd_nil n

/--
[factorialProd_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma factorialProd_cons_eq
  {a : ℕ}
  {L : List ℕ}
  {n : ℕ} :
-- imply
  factorialProd (a :: L) n =
    Nat.factorial (a * n) * factorialProd L n := by
-- proof
  apply factorialProd_cons a L n

/--
[factorialProd_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma factorialProd_perm_eq
  {L₁ L₂ : List ℕ}
  {n : ℕ}
-- given
  (h : List.Perm L₁ L₂) :
-- imply
  factorialProd L₁ n = factorialProd L₂ n := by
-- proof
  apply factorialProd_perm h n

/--
[factorialProd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma factorialProd_zero_eq
  {L : List ℕ} :
-- imply
  factorialProd L 0 = 1 := by
-- proof
  apply factorialProd_zero L

/--
[factorialProd_dvd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma factorialProd_dvd_zero_eq
  {A B : List ℕ} :
-- imply
  factorialProd B 0 ∣ factorialProd A 0 := by
-- proof
  apply factorialProd_dvd_zero A B

/--
[isIntegralFactorialRatio_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_iff_eq
  {A B : List ℕ} :
-- imply
  IsIntegralFactorialRatio A B ↔
    (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧ A.sum = B.sum ∧
    ∀ n : ℕ, factorialProd B n ∣ factorialProd A n := by
-- proof
  apply isIntegralFactorialRatio_iff A B

/--
[IsIntegralFactorialRatio.pos_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma IsIntegralFactorialRatio_pos_left_eq
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  ∀ a ∈ A, 0 < a := by
-- proof
  apply IsIntegralFactorialRatio.pos_left h

/--
[IsIntegralFactorialRatio.pos_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma IsIntegralFactorialRatio_pos_right_eq
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  ∀ b ∈ B, 0 < b := by
-- proof
  apply IsIntegralFactorialRatio.pos_right h

/--
[IsIntegralFactorialRatio.sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma IsIntegralFactorialRatio_sum_eq_eq
  {A B : List ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  A.sum = B.sum := by
-- proof
  apply IsIntegralFactorialRatio.sum_eq h

/--
[IsIntegralFactorialRatio.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma IsIntegralFactorialRatio_dvd_eq
  {A B : List ℕ}
  {n : ℕ}
-- given
  (h : IsIntegralFactorialRatio A B) :
-- imply
  factorialProd B n ∣ factorialProd A n := by
-- proof
  apply IsIntegralFactorialRatio.dvd h n

/--
[IsIntegralFactorialRatio.mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma IsIntegralFactorialRatio_mk_eq
  {A B : List ℕ}
-- given
  (hA : ∀ a ∈ A, 0 < a)
  (hB : ∀ b ∈ B, 0 < b)
  (hsum : A.sum = B.sum)
  (hdvd : ∀ n : ℕ, factorialProd B n ∣ factorialProd A n) :
-- imply
  IsIntegralFactorialRatio A B := by
-- proof
  apply IsIntegralFactorialRatio.mk hA hB hsum hdvd

/--
[isIntegralFactorialRatio_perm_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_perm_left_eq
  {A A' B : List ℕ}
-- given
  (hperm : List.Perm A A')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A' B := by
-- proof
  apply isIntegralFactorialRatio_perm_left hperm h

/--
[isIntegralFactorialRatio_perm_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_perm_right_eq
  {A B B' : List ℕ}
-- given
  (hperm : List.Perm B B')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A B' := by
-- proof
  apply isIntegralFactorialRatio_perm_right hperm h

/--
[isIntegralFactorialRatio_perm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_perm_eq
  {A A' B B' : List ℕ}
-- given
  (hA : List.Perm A A')
  (hB : List.Perm B B')
  (h : IsIntegralFactorialRatio A B) :
-- imply
  IsIntegralFactorialRatio A' B' := by
-- proof
  apply isIntegralFactorialRatio_perm hA hB h

/--
[isIntegralFactorialRatio_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_refl_eq
  {L : List ℕ}
-- given
  (hpos : ∀ a ∈ L, 0 < a) :
-- imply
  IsIntegralFactorialRatio L L := by
-- proof
  apply isIntegralFactorialRatio_refl L hpos

/--
[isIntegralFactorialRatio_singleton_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_singleton_self_eq
  {c : ℕ}
-- given
  (hc : 0 < c) :
-- imply
  IsIntegralFactorialRatio [c] [c] := by
-- proof
  apply isIntegralFactorialRatio_singleton_self c hc

/--
[isIntegralFactorialRatio_centralBinom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean)
-/
@[path]
private lemma isIntegralFactorialRatio_centralBinom_eq
  :
-- imply
  IsIntegralFactorialRatio [2] [1, 1] := by
-- proof
  apply isIntegralFactorialRatio_centralBinom


-- created on 2026-10-20
