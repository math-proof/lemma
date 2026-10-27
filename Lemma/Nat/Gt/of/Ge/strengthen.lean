import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℤ}
-- given
  (h : x > y) :
-- imply
  x ≥ y + 1 := by
-- proof
  omega


-- created on 2021-04-14
-- updated on 2026-10-26
