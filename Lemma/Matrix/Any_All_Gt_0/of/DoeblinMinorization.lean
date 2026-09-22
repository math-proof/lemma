import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h : DoeblinMinorization P) :
-- imply
  ∃ j, ∀ i, P i j > 0 := by
-- proof
  obtain ⟨ε, ν, hε0, -, hν, hP⟩ := h.minorize
  obtain ⟨j, hj⟩ : ∃ j, 0 < ν j := by
    by_contra hnone
    push Not at hnone
    have hz : ∀ j, ν j = 0 := fun j =>
      le_antisymm (hnone j) (hν.nonneg j)
    have : ∑ j, ν j = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hz j
    linarith [hν.rowsum]
  refine ⟨j, fun i => ?_⟩
  have hrow : P i j ≥ ε * ν j := hP i j
  nlinarith [hε0, hj, hrow]


-- created on 2026-09-22
