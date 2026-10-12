import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {p : Prop} [Decidable p]
  {f : ℝ} :
-- imply
  f * (if p then 1 else 0) ≥ 1 ↔ f ≥ 1 ∧ p := by
-- proof
  constructor
  ·
    intro h
    if hp : p then
      rw [ite_eq_left hp, mul_one] at h
      exact ⟨h, hp⟩
    else
      rw [ite_eq_right hp, mul_zero] at h
      exact absurd h (by norm_num)
  ·
    rintro ⟨h₀, h₁⟩
    rwa [ite_eq_left h₁, mul_one]


-- created on 2023-11-05
