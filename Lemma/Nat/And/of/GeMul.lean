import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ}
  {p : Prop}
  [Decidable p]
-- given
  (h : f * (if p then 1 else 0) ≥ 1) :
-- imply
  f ≥ 1 ∧ p := by
-- proof
  by_cases hp : p
  · rw [if_pos hp, mul_one] at h
    exact ⟨h, hp⟩
  · rw [if_neg hp, mul_zero] at h
    exact absurd h (by norm_num)


-- created on 2023-11-05
