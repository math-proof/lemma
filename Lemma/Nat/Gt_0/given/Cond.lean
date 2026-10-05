import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {p : Prop}
  [Decidable p]
-- given
  (h : (if p then (1 : ℝ) else 0) > 0) :
-- imply
  p := by
-- proof
  by_contra hp
  simp [hp] at h


-- created on 2023-11-05
