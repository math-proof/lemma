import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {ε r A : ℝ}
-- given
  (hε : ε ∈ Set.Ioo 0 1)
  (_hr : r > 0) :
-- imply
  min (r * A) (min (max r (1 - ε)) (1 + ε) * A) =
      if A ≥ 0 then (if r > 1 + ε then A * (1 + ε) else A * r) else (if r ≤ 1 - ε then A * (1 - ε) else A * r) := by
-- proof
  have key : min (r * A) (min (max r (1 - ε)) (1 + ε) * A) = A * (if A ≥ 0 then (if r > 1 + ε then 1 + ε else r) else (if r ≤ 1 - ε then 1 - ε else r)) := by
    obtain ⟨_, h₁⟩ := hε
    by_cases hA : A ≥ 0
    · rw [if_pos hA]
      by_cases hr₁ : r > 1 + ε
      · rw [if_pos hr₁, max_eq_left (by linarith), min_eq_right hr₁.le, min_eq_right (mul_le_mul_of_nonneg_right hr₁.le hA)]
        ring
      · rw [if_neg hr₁]
        have hc : r ≤ min (max r (1 - ε)) (1 + ε) := le_min (le_max_left _ _) (not_lt.mp hr₁)
        rw [min_eq_left (mul_le_mul_of_nonneg_right hc hA)]
        ring
    · rw [if_neg hA]
      replace hA : A < 0 := lt_of_not_ge hA
      by_cases hr₂ : r ≤ 1 - ε
      · rw [if_pos hr₂, max_eq_right hr₂, min_eq_left (show 1 - ε ≤ 1 + ε by linarith), min_eq_right (show (1 - ε) * A ≤ r * A by nlinarith)]
        ring
      · rw [if_neg hr₂]
        have hc : min (max r (1 - ε)) (1 + ε) ≤ r := (min_le_left _ _).trans (le_of_eq (max_eq_left (not_le.mp hr₂).le))
        rw [min_eq_left (show r * A ≤ min (max r (1 - ε)) (1 + ε) * A by nlinarith)]
        ring
  rw [key]
  split_ifs <;> rfl


-- created on 2023-03-31
