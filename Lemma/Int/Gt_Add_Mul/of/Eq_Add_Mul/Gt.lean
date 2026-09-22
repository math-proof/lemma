import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {b k x t y : α}
-- given
  (h₁ : k > 0)
  (h₀ : y = b + k * x)
  (h₂ : x > t) :
-- imply
  y > b + k * t := by
-- proof
  rcases h₀ with rfl
  have h₃ : k * t < k * x := mul_lt_mul_of_pos_left h₂ h₁
  have h₄ : b + k * t < b + k * x := add_lt_add_right h₃ b
  exact h₄


-- created on 2020-06-25
