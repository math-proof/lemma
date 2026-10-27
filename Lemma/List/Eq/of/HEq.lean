import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : List α}
  {b : List α}
-- given
  (h : HEq a b) :
-- imply
  a = b := by
-- proof
  simp_all


-- created on 2025-05-21
-- updated on 2026-10-26
