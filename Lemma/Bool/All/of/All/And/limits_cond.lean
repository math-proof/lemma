import sympy.Basic


@[path]
private lemma main
  {A : Set α}
  {p : α → Prop}
-- given
  (h : ∀ x ∈ A, p x) :
-- imply
  ∀ x ∈ A, p x ∧ x ∈ A :=
-- proof
  fun x hx => ⟨h x hx, hx⟩


-- created on 2018-12-12
