import sympy.Basic


@[main]
private lemma main
  {α : Sort u}
  {β : Sort v}
  {a₁ a₂ : α}
-- given
  (h : a₁ = a₂)
  (f : α → β) :
-- imply
  f a₁ = f a₂ :=
-- proof
  congrArg f h


-- created on 2018-04-03
-- updated on 2025-05-11
