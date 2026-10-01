import sympy.Basic


@[main]
private lemma transport
  {x y a : ℝ}
-- given
  (h : x + a ≥ y) :
-- imply
  x ≥ y - a := by
-- proof
  linarith


@[main]
private lemma transport.given
  {x y a : ℝ}
-- given
  (h : x ≥ y - a) :
-- imply
  x + a ≥ y := by
-- proof
  linarith


@[main]
private lemma strengthen
  {x y : ℝ}
-- given
  (h : x ≥ y + 1) :
-- imply
  x ≥ y := by
-- proof
  linarith


-- created on 2021-07-29
