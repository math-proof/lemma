import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  -- imply
  : ∑ k ∈ Finset.range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  -- proof
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    <;> ring

-- created on 2019-11-26
