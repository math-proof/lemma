import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddZeroClass R]
  {a : R} :
-- imply
  0 + a = a := by
-- proof
  rw [zero_add]


-- created on 2024-07-01
-- updated on 2026-10-26
