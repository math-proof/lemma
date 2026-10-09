import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  ∃ v : ℝ, v > 0 ∧ x > v := by
-- proof
  exact ⟨x / 2, by positivity, by linarith⟩


-- created on 2019-08-11
