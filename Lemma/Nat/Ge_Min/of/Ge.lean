import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [LinearOrder α]
-- given
  (h : c ≥ a)
  (b : α) :
-- imply
  c ≥ a ⊓ b := by
-- proof
  apply le_trans (min_le_left a b) h


-- created on 2025-05-14
-- updated on 2026-11-21
