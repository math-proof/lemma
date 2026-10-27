import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  {x : α}
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A ∧ x ∉ B :=
-- proof
  ⟨fun hx => h (Or.inl hx), fun hx => h (Or.inr hx)⟩


-- created on 2018-01-10
-- updated on 2026-10-26
