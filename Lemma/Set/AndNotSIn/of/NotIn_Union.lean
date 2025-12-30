import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  {x : α}
  (h : x ∉ A ∪ B) :
-- imply
  x ∉ A ∧ x ∉ B :=
-- proof
  ⟨fun hx => h (Or.inl hx), fun hx => h (Or.inr hx)⟩


-- created on 2025-04-05
-- updated on 2025-04-30
