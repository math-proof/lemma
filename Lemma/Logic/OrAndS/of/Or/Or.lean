import sympy.Basic


@[main]
private lemma main
  {R : α → β → Prop}
  {x : α}
  {a b : β}
-- given
  (h₀ : ¬p ∨ R x a)
  (h₁ : p ∨ R x b) :
-- imply
  R x a ∧ p ∨ R x b ∧ ¬p := by
-- proof
  by_cases hp : p <;>
  ·
    simp [hp] at *
    assumption


-- created on 2025-01-12
-- updated on 2025-04-11
