import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.Padics.Polynomial
open Polynomial


/--
[prime_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma prime_two : Nat.Prime 2 := by
decide

/--
[twelve_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma twelve_ne_zero : (12 : ℤ) ≠ 0 := by
decide

/--
[padicValInt_two_twelve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/Polynomial.lean)
-/
@[path]
private lemma padicValInt_two_twelve : padicValInt 2 (12 : ℤ) = 2 := by
  let _ := Fact.mk prime_two
  have h2 : 2 ≤ padicValInt 2 (12 : ℤ) := by
    obtain h | h := (padicValInt_dvd_iff (p := 2) 2 12).mp (by norm_num)
    · norm_num at h
    · exact h
  have h3 : ¬3 ≤ padicValInt 2 (12 : ℤ) := by
    intro h
    have hd : (2 : ℤ) ^ 3 ∣ 12 := (padicValInt_dvd_iff (p := 2) 3 12).mpr (Or.inr h)
    norm_num at hd
  omega


-- created on 2026-10-23
