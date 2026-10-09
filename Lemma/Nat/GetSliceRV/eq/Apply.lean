import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- `x[:n]` for a family of random variables: the random vector `ω ↦ (x 0 ω, …, x (n-1) ω)`. -/
@[path]
private lemma main
-- given
  (x : ℕ → Ω → α)
  (n : ℕ)
  (ω : Ω)
  (i : Fin n) :
-- imply
  x[:n] ω i = x i ω := by
-- proof
  exact rfl


-- created on 2026-10-07
