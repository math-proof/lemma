import sympy.Basic


@[path]
private lemma limits_cond.given
  {A : Set α}
  {p : α → Prop}
-- given
  (h : ∀ x ∈ A, p x ∧ x ∈ A) :
-- imply
  ∀ x ∈ A, p x :=
-- proof
  fun x hx => (h x hx).1


-- created on 2018-12-12
