import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a > b) :
-- imply
  (a + b) / 2 ∈ Set.Ioo b a := by
-- proof
  constructor <;> linarith


-- created on 2021-04-16
