import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {p : Prop}
  [Decidable p] :
-- imply
  (if p then (1 : ℝ) else 0) > 0 ↔ p := by
-- proof
  by_cases hp : p <;> simp [hp]


-- created on 2023-11-05
