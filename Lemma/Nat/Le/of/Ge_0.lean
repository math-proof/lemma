import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a - b ≥ 0) :
-- imply
  b ≤ a := by
-- proof
  linarith


@[path]
private lemma given
  {x y : ℝ}
-- given
  (h : y - x ≥ 0) :
-- imply
  x ≤ y := by
-- proof
  linarith


@[path]
private lemma scale
  {a t : ℝ}
-- given
  (h₀ : a ≥ 0)
  (h₁ : t ≤ 1) :
-- imply
  t * a ≤ a := by
-- proof
  nlinarith


-- created on 2019-11-08
