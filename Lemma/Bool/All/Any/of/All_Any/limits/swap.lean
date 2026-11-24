import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {Sx : Set α}
  {Sy : Set β}
  {p : α → β → Prop}
-- given
  (h : ∀ x ∈ Sx, ∃ y ∈ Sy, p x y) :
-- imply
  ∀ y ∈ Sx, ∃ x ∈ Sy, p y x :=
-- proof
  h


-- created on 2021-09-19
-- updated on 2026-11-24
