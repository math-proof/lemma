import sympy.Basic
import sympy.stats.stochastic_process_types


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {ν : S → ℝ}
-- given
  (hν : StochasticVec ν) :
-- imply
  RowStochastic (broadcast ν : Matrix S S ℝ) := by
-- proof
  constructor
  intro i
  convert hν
  funext j
  simp [broadcast]


-- created on 2026-09-24
