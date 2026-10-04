import sympy.Basic


@[main]
private lemma main
  {x y a : ℝ}
-- given
  (h : x + a ≠ y + a) :
-- imply
  x ≠ y := by
-- proof
  intro heq
  apply h
  rw [heq]


-- created on 2020-02-03
