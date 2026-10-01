import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  linarith


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x < y) :
-- imply
  x - y < 0 := by
-- proof
  linarith


@[main]
private lemma transit
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : y ≤ 0) :
-- imply
  x < 0 := by
-- proof
  linarith


-- created on 2023-04-15
