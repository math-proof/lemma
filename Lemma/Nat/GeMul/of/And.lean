import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {f : ℝ}
  {p : Prop}
  [Decidable p]
-- given
  (h₀ : f ≥ 1)
  (h₁ : p) :
-- imply
  f * (if p then 1 else 0) ≥ 1 := by
-- proof
  rw [if_pos h₁, mul_one]
  exact h₀


-- created on 2023-11-05
