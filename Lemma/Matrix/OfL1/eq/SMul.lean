import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
-- given
  (c : ℝ) (x : S → ℝ) :
-- imply
  ofL1 (c • x) = c • ofL1 x := by
-- proof
  ext
  simp [ofL1]


-- created on 2026-09-22
