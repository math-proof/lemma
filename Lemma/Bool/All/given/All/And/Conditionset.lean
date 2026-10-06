import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {p c : α → Prop}
-- given
  (h : ∀ x ∈ {x ∈ A | c x}, p x) :
-- imply
  ∀ x ∈ {x ∈ A | c x}, p x ∧ c x :=
-- proof
  fun x hx => ⟨h x hx, hx.2⟩


-- created on 2018-12-11
