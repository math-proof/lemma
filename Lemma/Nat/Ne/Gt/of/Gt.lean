import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℝ}
-- given
  (h : x > a) :
-- imply
  x ≠ a ∧ x > a - 1 := by
-- proof
  exact ⟨ne_of_gt h, by linarith⟩


-- created on 2023-04-13
