import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℤ}
-- given
  (h : |x| ≤ a) :
-- imply
  x ≤ a ∧ x ≥ -a := by
-- proof
  exact ⟨(abs_le.mp h).2, (abs_le.mp h).1⟩


-- created on 2023-04-15
