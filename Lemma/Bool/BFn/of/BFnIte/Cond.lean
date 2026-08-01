import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {a b : α}
-- given
  (h₀ : p)
  (h₁ : R (if p then
    a
  else
    b) c) :
-- imply
  R a c := by
-- proof
  simp_all


-- created on 2018-01-06
