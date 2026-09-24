import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (m n : ℕ)
  (i j k : S) :
-- imply
  (P ^ (m + n)) i j ≥ (P ^ m) i k * (P ^ n) k j := by
-- proof
  have := smat_pow_is_smat (P := P) m
  have := smat_pow_is_smat (P := P) n
  rw [pow_add]
  simp [Matrix.mul_apply]
  rw [← Finset.sum_erase_add (a := k)]
  ·
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro l hl
    apply mul_nonneg <;>
      apply (RowStochastic.stochastic _).nonneg
  · simp


-- created on 2026-09-19
