import sympy.Basic


@[main]
private lemma main
  [LE α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  y ≥ x := by
-- proof
  exact h


@[main]
private lemma reverse.given
  {a x : ℝ}
-- given
  (h : a ≤ x) :
-- imply
  x ≥ a := by
-- proof
  exact h


@[main]
private lemma reverse
  {a x : ℝ}
-- given
  (h : x ≤ a) :
-- imply
  a ≥ x := by
-- proof
  exact h


-- created on 2019-05-24
-- updated on 2026-09-27
