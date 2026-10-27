import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddZeroClass R]
  {a : R} :
-- imply
  a + 0 = a := by
-- proof
  rw [add_zero]


-- created on 2024-07-01
-- updated on 2026-10-26
