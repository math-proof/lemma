import sympy.Basic


@[path]
private lemma limits.swap
  {Sx : Set α}
  {Sy : Set β}
  {p : α → β → Prop}
-- given
  (h : ∀ x ∈ Sx, ∃ y ∈ Sy, p x y) :
-- imply
  ∀ y ∈ Sx, ∃ x ∈ Sy, p y x :=
-- proof
  h


-- created on 2026-09-27
