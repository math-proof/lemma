import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {a b : α}
-- given
  (h₁ : p ∧ R a c) :
-- imply
  p ∧ R (if p then
    a
  else
    b) c := by
-- proof
  simp_all


-- created on 2025-07-29
