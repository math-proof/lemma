import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (ascPochhammer ℝ k).eval x * (Nat.stirlingSecond n k : ℝ) * (-1) ^ (n - k) = x ^ n := by
-- proof
  have key : ∀ (x : ℝ) (n : ℕ), ∑ k ∈ Finset.range (n + 1), (descPochhammer ℝ k).eval x * (Nat.stirlingSecond n k : ℝ) = x ^ n := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      have hD : ∀ k : ℕ, (descPochhammer ℝ k).eval x * x = (descPochhammer ℝ (k + 1)).eval x + k * (descPochhammer ℝ k).eval x := by
        intro k
        rw [descPochhammer_succ_eval]
        ring
      have A : ∑ k ∈ Finset.range (n + 1 + 1), (descPochhammer ℝ k).eval x * (Nat.stirlingSecond (n + 1) k : ℝ) =
          ∑ j ∈ Finset.range (n + 1), (descPochhammer ℝ (j + 1)).eval x * (Nat.stirlingSecond n j : ℝ) +
          ∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * (descPochhammer ℝ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℝ) := by
        rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.stirlingSecond_succ_succ]
        push_cast
        ring
      have B : ∑ j ∈ Finset.range (n + 1), ((j : ℝ) + 1) * (descPochhammer ℝ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℝ) =
          ∑ k ∈ Finset.range (n + 1), (k : ℝ) * (descPochhammer ℝ k).eval x * (Nat.stirlingSecond n k : ℝ) := by
        rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, add_zero,
          Finset.sum_range_succ']
        simp
      rw [A, B, pow_succ, ← ih, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      linear_combination (-(Nat.stirlingSecond n k : ℝ)) * hD k
  have e := key (-x) n
  rw [show x ^ n = (-1) ^ n * (-x) ^ n by rw [← mul_pow]; ring, ← e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have ha := ascPochhammer_eval_neg_eq_descPochhammer ℝ (-x) k
  rw [neg_neg] at ha
  have hp : (-1 : ℝ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [ha, hp]
  ring


-- created on 2023-08-26
