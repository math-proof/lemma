import sympy.sets.sets
import sympy.functions.elementary.trigonometric
import Lemma.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : x ∈ Icc (-(π / 2)) (π / 2))
  (h₂ : y ∈ Icc (-(π / 2)) (π / 2)) :
-- imply
  sin x < sin y := by
-- proof
  -- Extract the bounds for x and y from the interval membership conditions.
  let ⟨h₁_left, h₁_right⟩ := h₁
  let ⟨h₂_left, h₂_right⟩ := h₂
  -- Use the fact that the sine function is strictly increasing on [0, π/2].
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  -- Verify the conditions for the sine function's strict monotonicity.
  linarith [h₁_left, h₁_right, h₂_left, h₂_right]
  -- Use linear arithmetic to confirm the interval bounds and the inequality.
  linarith [Real.sin_le_one x, Real.sin_le_one y]
  assumption


-- created on 2025-03-24
-- updated on 2025-03-25
