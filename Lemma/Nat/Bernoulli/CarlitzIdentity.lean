import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.CarlitzIdentity
open Nat Finset
open MetaMathlibExt


namespace MetaMathlibExt

/--
[S_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma S_succ (m n : ℕ) : S (m + 1) n = S m n + S m (n + 1) := by
  simp only [S]
  rw [sum_range_succ']
  simp only [choose_zero_right, Nat.cast_one, one_mul, add_zero]
  simp_rw [choose_succ_succ, Nat.cast_add, add_mul]
  rw [sum_add_distrib]
  have hfirst :
    (∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + (x + 1))) =
      ∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + 1 + x) := by
    apply sum_congr rfl
    intro x hx
    rw [Nat.add_comm x 1, ← Nat.add_assoc]
  have hshift :
    (∑ x ∈ range (m + 1), (m.choose x.succ : ℚ) * bernoulli (n + (x + 1))) +
      bernoulli n =
      ∑ x ∈ range (m + 1), (m.choose x : ℚ) * bernoulli (n + x) := by
    rw [sum_range_succ, sum_range_succ']
    simp [add_comm, add_left_comm]
  rw [hfirst, ← hshift]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[A_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma A_zero_left (n : ℕ) : A 0 n = bernoulli n := by
  simp [A, S]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[A_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma A_zero_right (n : ℕ) : A n 0 = bernoulli n := by
  rw [A]
  have h := Polynomial.bernoulli_eval_one n
  rw [Polynomial.bernoulli] at h
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one] at h
  rw [show S n 0 = bernoulli' n by simpa [S, mul_comm] using h]
  simp [bernoulli'_eq_bernoulli, ← mul_assoc, ← sq, ← pow_mul, mul_comm n 2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[A_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma A_succ (m n : ℕ) :
  A (m + 1) n = -A m n - A m (n + 1) := by
  simp only [A, S_succ, pow_succ]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[A_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma A_symm (m n : ℕ) : A m n = A n m := by
  induction m generalizing n with
  | zero => rw [A_zero_left, A_zero_right]
  | succ m ih =>
    rw [A_succ, ih n, ih (n + 1), A_succ]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[carlitz_bernoulli_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
lemma carlitz_bernoulli_sum_symm
  {m n : ℕ} :
-- imply
  (-1 : ℚ) ^ m * (Finset.range (m + 1)).sum
    (fun k => (Nat.choose m k : ℚ) * bernoulli (n + k)) =
    (-1 : ℚ) ^ n * (Finset.range (n + 1)).sum
    (fun k => (Nat.choose n k : ℚ) * bernoulli (m + k)) := by
-- proof
  exact A_symm m n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
