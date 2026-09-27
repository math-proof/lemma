import sympy.Basic
import sympy.stats.stochastic_process_types
open scoped Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {μ : S → ℝ} [StochasticVec μ]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (h₀ : Stationary μ P)
  {n : ℕ} :
-- imply
  Stationary μ (P ^ n) := by
-- proof
  constructor
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.vecMul_vecMul, ih, h₀.stationary]


-- created on 2026-09-19
-- updated on 2026-09-26
