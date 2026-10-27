import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : α → Prop}
  {A : Set α}

-- given
  (h : ∀ x ∈ A, p x)
  (x : α):
-- imply
  p x ∨ x ∉ A := by
-- proof
  grind


-- created on 2018-12-02
-- updated on 2026-10-26
