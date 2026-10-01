import sympy.sets.sets
import sympy.Basic


@[main]
private lemma average
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  (x + y) / 2 ∈ Set.Ioo x y := by
-- proof
  exact ⟨by linarith, by linarith⟩


-- created on 2019-06-21
