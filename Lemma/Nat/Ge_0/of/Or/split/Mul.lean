import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : x ≥ 0 ∧ y ≥ 0 ∨ x ≤ 0 ∧ y ≤ 0) :
-- imply
  x * y ≥ 0 := by
-- proof
  rcases h with ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ <;> nlinarith


-- created on 2023-04-15
