import sympy.Basic


@[main]
private lemma main
  {p : Prop}
  {q : α → Prop}
  {x a : α} :
-- imply
  x = a ∧ p → q x ↔ x = a ∧ p → q a := by
-- proof
  constructor <;>
  ·
    intro h₀ h₁
    have := h₀ h₁
    simp_all


-- created on 2018-02-06
