import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊓ b = b :=
-- proof
  min_eq_right (le_of_lt h)


-- created on 2018-09-09
-- updated on 2026-11-23
