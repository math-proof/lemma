import sympy.Basic


@[main]
private lemma given
  {A : Set α}
  {p q : α → Prop}
-- given
  (h : ∀ x ∈ A, q x) :
-- imply
  ∀ x ∈ A, p x ∨ q x :=
-- proof
  fun x hx => Or.inr (h x hx)


-- created on 2019-02-05
