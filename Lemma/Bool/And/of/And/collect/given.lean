import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (h : f ∧ (c ∨ a ∧ x)) :
-- imply
  (a ∨ c) ∧ f ∧ (x ∨ c) := by
-- proof
  tauto




-- created on 2019-04-29
-- updated on 2026-11-24
