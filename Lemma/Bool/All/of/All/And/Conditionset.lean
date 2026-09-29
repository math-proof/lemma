import sympy.Basic


@[main]
private lemma given
  {A : Set α}
  {p c : α → Prop}
-- given
  (h : ∀ x ∈ {x ∈ A | c x}, p x ∧ c x) :
-- imply
  ∀ x ∈ {x ∈ A | c x}, p x :=
-- proof
  fun x hx => (h x hx).1


-- created on 2026-09-27
