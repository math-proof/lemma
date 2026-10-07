import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- `f[:n]` for a plain sequence `f : ℕ → α`. -/
@[main]
private lemma main
-- given
  (f : ℕ → α)
  (n : ℕ)
  (i : Fin n) :
-- imply
  f[:n] i = f i := by
-- proof
  exact rfl


-- created on 2026-10-07
