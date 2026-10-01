import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℝ}
-- given
  (h : x < -a ∨ x > a) :
-- imply
  |x| > a := by
-- proof
  rcases h with h | h
  · have := neg_abs_le x
    linarith
  · have := le_abs_self x
    linarith


-- created on 2018-07-31
