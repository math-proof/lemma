import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℝ}
  {p : Prop}
  [Decidable p] :
-- imply
  f * (if p then 1 else 0) ≥ 1 ↔ f ≥ 1 ∧ p := by
-- proof
  constructor
  · intro h
    by_cases hp : p
    · rw [if_pos hp, mul_one] at h
      exact ⟨h, hp⟩
    · rw [if_neg hp, mul_zero] at h
      exact absurd h (by norm_num)
  · rintro ⟨h₀, h₁⟩
    rw [if_pos h₁, mul_one]
    exact h₀


-- created on 2023-11-05
