import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℤ} :
-- imply
  x ^ n = ∑ k ∈ Finset.range (n + 1), (descPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) := by
-- proof
  have key : ∀ (x : ℤ) (n : ℕ), ∑ k ∈ Finset.range (n + 1), (descPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) = x ^ n := by
    intro x n
    induction n with
    | zero => simp
    | succ n ih =>
      have hD : ∀ k : ℕ, (descPochhammer ℤ k).eval x * x = (descPochhammer ℤ (k + 1)).eval x + k * (descPochhammer ℤ k).eval x := by
        intro k
        rw [descPochhammer_succ_eval]
        ring
      have A : ∑ k ∈ Finset.range (n + 1 + 1), (descPochhammer ℤ k).eval x * (Nat.stirlingSecond (n + 1) k : ℤ) =
          ∑ j ∈ Finset.range (n + 1), (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n j : ℤ) +
          ∑ j ∈ Finset.range (n + 1), ((j : ℤ) + 1) * (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℤ) := by
        rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.stirlingSecond_succ_succ]
        push_cast
        ring
      have B : ∑ j ∈ Finset.range (n + 1), ((j : ℤ) + 1) * (descPochhammer ℤ (j + 1)).eval x * (Nat.stirlingSecond n (j + 1) : ℤ) =
          ∑ k ∈ Finset.range (n + 1), (k : ℤ) * (descPochhammer ℤ k).eval x * (Nat.stirlingSecond n k : ℤ) := by
        rw [Finset.sum_range_succ, Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n), Nat.cast_zero, mul_zero, add_zero,
          Finset.sum_range_succ']
        simp
      rw [A, B, pow_succ, ← ih, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      linear_combination (-(Nat.stirlingSecond n k : ℤ)) * hD k
  exact (key x n).symm


-- created on 2023-08-26
