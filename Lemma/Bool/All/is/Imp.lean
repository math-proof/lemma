import sympy.Basic


@[main]
private lemma main
  {p c : α → Prop} :
-- imply
  (∀ x ∈ {x | c x}, p x) ↔ ∀ x, c x → p x :=
-- proof
  Iff.rfl


-- created on 2018-12-22
