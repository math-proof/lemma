import sympy.sets.sets
import sympy.Basic


@[main]
private lemma telescope
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.Ico 1 (n + 1), 1 / ((k : ℝ) * (k + 1)) = 1 - 1 / (n + 1) := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    field_simp
    ring


-- created on 2023-08-17
