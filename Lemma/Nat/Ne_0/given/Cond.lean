import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {p : Prop}
  [Decidable p]
-- given
  (h : (if p then 1 else 0 : ℤ) ≠ 0) :
-- imply
  p := by
-- proof
  by_contra hp
  simp [hp] at h


-- created on 2023-11-05
-- updated on 2025-04-20
