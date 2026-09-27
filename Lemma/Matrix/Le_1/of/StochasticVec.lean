import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {x : S → ℝ}
-- given
  (h₀ : StochasticVec x)
  (s : S) :
-- imply
  x s ≤ 1 := by
-- proof
  rw [← h₀.rowsum]
  apply Finset.single_le_sum (fun z _ => h₀.nonneg z) (Finset.mem_univ s)


-- created on 2026-09-19
-- updated on 2026-09-26
