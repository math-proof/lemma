import sympy.Basic


@[main]
private lemma subst
  {p : α → Prop}
  {y : α}
-- given
  (h : ∀ x, p x) :
-- imply
  p y :=
-- proof
  h y


-- created on 2026-09-27
