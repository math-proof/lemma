import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {A : Set α}
-- given
  (h : ∀ x, x ∉ A ∨ p x) :
-- imply
  ∀ x ∈ A, p x := by
-- proof
  grind


-- created on 2026-10-03
