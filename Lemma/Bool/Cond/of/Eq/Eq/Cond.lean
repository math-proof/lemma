import sympy.Basic


@[main]
private lemma subst
  {a a' : α}
  {b b' : β}
  {P : α → β → Prop}
-- given
  (h₀ : a = a')
  (h₁ : b = b')
  (h₂ : P a b) :
-- imply
  P a' b' := by
-- proof
  rwa [← h₀, ← h₁]


-- created on 2021-09-11
