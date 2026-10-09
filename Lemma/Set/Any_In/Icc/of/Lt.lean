import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  ∃ x : ℝ, x ∈ Set.Ioo a b := by
-- proof
  exact ⟨(a + b) / 2, by linarith, by linarith⟩


-- created on 2019-12-23
