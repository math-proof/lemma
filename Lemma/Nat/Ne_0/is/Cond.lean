import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {p : Prop}
  [Decidable p] :
-- imply
  (if p then 1 else 0 : ℤ) ≠ 0 ↔ p := by
-- proof
  by_cases h : p
  · simp [h]
  · simp [h]


-- created on 2023-11-05
