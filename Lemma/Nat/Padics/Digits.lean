import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.Digits
open PadicInt


/--
[padicDigit_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma padicDigit_lt_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  padicDigit a n < p := by
-- proof
  apply PadicInt.padicDigit_lt a n

/--
[padicExpansion_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma padicExpansion_val_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  (padicExpansion a n).val = padicDigit a n := by
-- proof
  apply PadicInt.padicExpansion_val a n

/--
[padicDigit_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma padicDigit_mul_pow_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n := by
-- proof
  apply PadicInt.padicDigit_mul_pow a n

/--
[appr_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma appr_succ_eq_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr (n + 1) = a.appr n + padicDigit a n * p ^ n := by
-- proof
  apply PadicInt.appr_succ_eq a n

/--
[appr_succ_eq_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma appr_succ_eq_val_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr (n + 1) = a.appr n + (padicExpansion a n).val * p ^ n := by
-- proof
  apply PadicInt.appr_succ_eq_val a n

/--
[appr_eq_sum_padicDigit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma appr_eq_sum_padicDigit_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr n = ∑ k ∈ Finset.range n, padicDigit a k * p ^ k := by
-- proof
  apply PadicInt.appr_eq_sum_padicDigit a n

/--
[appr_eq_sum_expansion_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
private lemma appr_eq_sum_expansion_val_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr n = ∑ k ∈ Finset.range n, (padicExpansion a k).val * p ^ k := by
-- proof
  apply PadicInt.appr_eq_sum_expansion_val a n


-- created on 2026-10-20
