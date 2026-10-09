import sympy.functions.combinatorial.integer_factorials
import sympy.Basic
import Lemma.Finset.EvalAscPochhammer.eq.Sum_MulPowStirlingFirst
open Finset


/-- `FallingFactorial(x, n) = Σ_{k ≤ n} x^k · Stirling1(n, k) · (-1)^(n-k)`. -/
@[path]
private lemma main
-- given
  (x : ℝ)
  (n : ℕ) :
-- imply
  (descPochhammer ℝ n).eval x =
      ∑ k ∈ Finset.range (n + 1), x ^ k * (Nat.stirlingFirst n k : ℝ) * (-1) ^ (n - k) := by
-- proof
  have e := ascPochhammer_eval_neg_eq_descPochhammer ℝ x n
  have s := EvalAscPochhammer.eq.Sum_MulPowStirlingFirst (-x) n
  have hd : (descPochhammer ℝ n).eval x = (-1) ^ n * (ascPochhammer ℝ n).eval (-x) := by
    rw [e, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [hd, s, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by rw [Finset.mem_range] at hk; omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, neg_pow x k]
  have hk2 : ((-1 : ℝ)) ^ k * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  linear_combination (x ^ k * (Nat.stirlingFirst (k + j) k : ℝ) * (-1) ^ j) * hk2


-- created on 2026-10-07
