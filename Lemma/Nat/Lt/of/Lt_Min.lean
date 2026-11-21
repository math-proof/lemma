import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : x < a ⊓ b) :
-- imply
  x < b := by
-- proof
  apply lt_of_lt_of_le h (min_le_right a b)


-- created on 2020-01-11
-- updated on 2026-11-21
