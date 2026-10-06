import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
-- given
  (hgt : y < x)
  (h : y ∈ Set.Icc a b) :
-- imply
  a < x := by
-- proof
  linarith [h.1]


-- created on 2020-11-25
