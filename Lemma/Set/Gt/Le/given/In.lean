import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (hgt : x < b)
  (hle : a ≤ x) :
-- imply
  x ∈ Set.Ico a b := by
-- proof
  exact ⟨hle, hgt⟩


-- created on 2021-04-19
