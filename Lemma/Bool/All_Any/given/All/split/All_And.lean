import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {p q r : α → Prop}
-- given
  (h : ∀ x ∈ A, p x ∧ q x ∧ r x) :
-- imply
  (∀ x ∈ A, p x) ∧ (∀ x ∈ A, q x) ∧ (∀ x ∈ A, r x) := by
-- proof
  refine ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2.1, fun x hx => (h x hx).2.2⟩


-- created on 2021-08-25
