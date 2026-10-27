import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  x ≠ y :=
-- proof
  ne_of_lt h


-- created on 2021-01-12
-- updated on 2026-10-26
