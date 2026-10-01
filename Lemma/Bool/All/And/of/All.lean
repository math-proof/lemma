import sympy.Basic


@[main]
private lemma main
  {g f : α → Prop}
-- given
  (h : ∀ x, g x → f x) :
-- imply
  ∀ x, g x → f x ∧ g x :=
-- proof
  fun x hx => ⟨h x hx, hx⟩


-- created on 2018-12-17
