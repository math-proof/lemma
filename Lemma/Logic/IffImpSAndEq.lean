import Lemma.Basic


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
    -- Apply h₀ to h₁ to get q(x)
    simp_all


-- created on 2025-04-10
