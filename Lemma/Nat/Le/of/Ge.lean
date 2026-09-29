import sympy.Basic


@[main]
private lemma main
  [LE α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  y ≤ x := by
-- proof
  exact h


@[main]
private lemma reverse.given
  {x a : ℝ}
-- given
  (h : a ≥ x) :
-- imply
  x ≤ a := by
-- proof
  exact h


@[main]
private lemma reverse
  {x a : ℝ}
-- given
  (h : x ≥ a) :
-- imply
  a ≤ x := by
-- proof
  exact h


-- created on 2019-10-29
-- updated on 2026-09-27
