import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {p : Prop} [Decidable p]
  {f : ℝ}
-- given
  (h₀ : f ≥ 1)
  (h₁ : p) :
-- imply
  f * (if p then 1 else 0) ≥ 1 := by
-- proof
  rwa [ite_eq_left h₁, mul_one]


-- created on 2023-11-05
