import sympy.functions.combinatorial.integer_factorials
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma telescope
  {n i : ℕ}
-- given
  (h : i > 0) :
-- imply
  ∑ k ∈ Finset.range n, FallingFactorial (k : ℝ) (-(i : ℤ) - 1) = (1 / (Nat.factorial i : ℝ) - FallingFactorial (n : ℝ) (-(i : ℤ))) / i := by
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
  have ff : ∀ (y : ℝ) (m : ℕ), m > 0 → FallingFactorial y (-(m : ℤ)) = 1 / (ascPochhammer ℝ m).eval (y + 1) := by
    intro y m hm
    simp only [FallingFactorial]
    rw [if_neg (by omega), show (-(-(m : ℤ))).toNat = m by omega, descPochhammer_eval_eq_ascPochhammer]
    push_cast
    ring_nf
  rw [ff _ i h, ← key n]
  apply Finset.sum_congr rfl
  intro k _
  rw [show -(i : ℤ) - 1 = -((i + 1 : ℕ) : ℤ) by push_cast; ring, ff _ (i + 1) (by omega)]


-- created on 2026-09-27
