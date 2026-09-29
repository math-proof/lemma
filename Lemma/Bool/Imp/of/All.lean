import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
  {x : α}
-- given
  (h : ∀ x, p x → q x) :
-- imply
  p x → q x :=
-- proof
  h x


-- created on 2026-09-27
