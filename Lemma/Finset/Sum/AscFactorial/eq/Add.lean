import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Combinatorics.Enumerative.Stirling
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma telescope
  {n i : ℕ}
-- given
  (h : i > 0) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, 1 / (ascPochhammer ℝ (i + 1)).eval (k : ℝ) = (1 / (Nat.factorial i : ℝ) - 1 / (ascPochhammer ℝ i).eval ((n : ℝ) + 1)) / i := by
-- proof
  have key : ∀ n : ℕ, ∑ k ∈ Finset.range n, 1 / (ascPochhammer ℝ (i + 1)).eval ((k : ℝ) + 1) =
      (1 / (Nat.factorial i : ℝ) - 1 / (ascPochhammer ℝ i).eval ((n : ℝ) + 1)) / i := by
    have hi : (i : ℝ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
    intro n
    induction n with
    | zero =>
      rw [Finset.sum_range_zero, Nat.cast_zero, zero_add, ascPochhammer_eval_one]
      ring
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have ha : 0 < (ascPochhammer ℝ i).eval ((n : ℝ) + 1) := ascPochhammer_pos _ _ (by positivity)
      have hb : 0 < (ascPochhammer ℝ i).eval ((n : ℝ) + 1 + 1) := ascPochhammer_pos _ _ (by positivity)
      have e1 : (ascPochhammer ℝ (i + 1)).eval ((n : ℝ) + 1) = (ascPochhammer ℝ i).eval ((n : ℝ) + 1) * ((n : ℝ) + 1 + i) :=
        ascPochhammer_succ_eval _ _
      have e2 : (ascPochhammer ℝ (i + 1)).eval ((n : ℝ) + 1) = ((n : ℝ) + 1) * (ascPochhammer ℝ i).eval ((n : ℝ) + 1 + 1) := by
        rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_one]
      push_cast
      rw [e1]
      field_simp
      linear_combination (-(Nat.factorial i : ℝ)) * e2.symm.trans e1
  have conv : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, 1 / (ascPochhammer ℝ (i + 1)).eval (k : ℝ) =
      ∑ k ∈ Finset.range m, 1 / (ascPochhammer ℝ (i + 1)).eval ((k + 1 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  rw [conv n]
  simp only [Nat.cast_add, Nat.cast_one]
  exact key n


-- created on 2026-09-27
