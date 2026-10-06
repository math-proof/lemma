import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
-- given
  (h : a < b) :
-- imply
  ∃ x : ℤ, x ∈ Set.Ico a b := by
-- proof
  exact ⟨b - 1, by linarith, by linarith⟩


-- created on 2021-04-18
