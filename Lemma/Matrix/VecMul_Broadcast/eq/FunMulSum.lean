import sympy.Basic
import sympy.stats.stochastic_process_types
open scoped Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {ν : S → ℝ}
-- given
  (v : S → ℝ) :
-- imply
  v ᵥ* broadcast ν = fun j => (∑ i, v i) * ν j := by
-- proof
  funext j
  simp [broadcast, Matrix.vecMul, Finset.sum_mul, dotProduct]


-- created on 2026-09-19
-- updated on 2026-09-26
