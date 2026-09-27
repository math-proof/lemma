import sympy.Basic
import sympy.stats.stochastic_process_types
open scoped Matrix BigOperators


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A B : Matrix S S ℝ} [RowStochastic A] [RowStochastic B]
  {ε : ℝ}
-- given
  (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  RowStochastic (ε • A + (1 - ε) • B) := by
-- proof
  have hε0 : 0 ≤ ε := hε.1
  have hε1 : 0 ≤ 1 - ε := by grind [hε.2]
  constructor
  intro i
  constructor
  · intro j
    have hA := (inferInstance : RowStochastic A).stochastic i
    have hB := (inferInstance : RowStochastic B).stochastic i
    have hnn := add_nonneg (mul_nonneg hε0 (hA.nonneg j)) (mul_nonneg hε1 (hB.nonneg j))
    simpa [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] using hnn
  · have hA := (inferInstance : RowStochastic A).stochastic i
    have hB := (inferInstance : RowStochastic B).stochastic i
    calc
      _ = ∑ j, (ε * A i j + (1 - ε) * B i j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      _ = ε * ∑ j, A i j + (1 - ε) * ∑ j, B i j := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = ε * 1 + (1 - ε) * 1 := by
        rw [hA.rowsum, hB.rowsum]
      _ = 1 := by
        ring


-- created on 2026-09-24
