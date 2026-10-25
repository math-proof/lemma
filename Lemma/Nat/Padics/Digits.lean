import Mathlib
import sympy.Basic
import Theorem.NumberTheory.Padics.Digits.Part2
open PadicInt


namespace PadicInt

/--
[padicDigit_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma padicDigit_mul_pow
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  padicDigit a n * p ^ n = a.appr (n + 1) - a.appr n := by
-- proof
  unfold padicDigit
  exact Nat.div_mul_cancel (dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n))

end PadicInt

namespace PadicInt

/--
[appr_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma appr_succ_eq
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr (n + 1) = a.appr n + padicDigit a n * p ^ n := by
-- proof
  have hle : a.appr n ≤ a.appr (n + 1) := appr_mono a (Nat.le_succ n)
  have h := padicDigit_mul_pow a n
  omega

end PadicInt

namespace PadicInt

/--
[appr_succ_eq_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma appr_succ_eq_val
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr (n + 1) = a.appr n + (padicExpansion a n).val * p ^ n := by
-- proof
  simpa using appr_succ_eq a n

end PadicInt

namespace PadicInt

/--
[appr_eq_sum_padicDigit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma appr_eq_sum_padicDigit
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr n = ∑ k ∈ Finset.range n, padicDigit a k * p ^ k := by
-- proof
  induction n with
  | zero => simp [appr]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, appr_succ_eq]

end PadicInt

namespace PadicInt

/--
[appr_eq_sum_expansion_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean)
-/
@[path]
lemma appr_eq_sum_expansion_val
  {p : Nat} [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : Nat} :
-- imply
  a.appr n = ∑ k ∈ Finset.range n, (padicExpansion a k).val * p ^ k := by
-- proof
  simpa using appr_eq_sum_padicDigit a n

end PadicInt

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


-- created on 2026-10-20
-- updated on 2026-10-23
