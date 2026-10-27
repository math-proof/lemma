import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Decidable c]
  {a b : α}
  {q : α → Prop}
-- given
  (h : p ∧ c → q (if c then a else b)) :
-- imply
  p ∧ c → q a := by
-- proof
  intro hpc
  have h' := h hpc
  rwa [ite_eq_left hpc.2] at h'


-- created on 2023-04-25
-- updated on 2026-10-26
