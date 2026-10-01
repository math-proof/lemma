import sympy.sets.sets
import sympy.Basic


@[main]
private lemma restrict
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Ico a (b - 1)) :
-- imply
  x ∈ Set.Ico a b := by
-- proof
  exact ⟨h.1, by linarith [h.2]⟩


-- created on 2023-08-20
