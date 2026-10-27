import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  ∃ y > 0, x = y :=
-- proof
  ⟨x, h, rfl⟩


-- created on 2018-08-23
-- updated on 2026-10-26
