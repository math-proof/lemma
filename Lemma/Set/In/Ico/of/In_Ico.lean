import sympy.sets.sets
import sympy.Basic


@[main]
private lemma relax
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  x ∈ Set.Ico a (b + 1) := by
-- proof
  exact ⟨h.1, by linarith [h.2]⟩


-- created on 2026-09-27
