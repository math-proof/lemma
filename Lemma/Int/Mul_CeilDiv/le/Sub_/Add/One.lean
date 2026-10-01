import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x d : ℤ}
-- given
  (h : d > 0) :
-- imply
  ⌈(x : ℝ) / d⌉ * d ≤ x + d - 1 := by
-- proof
  have h₁ := Int.ceil_lt_add_one ((x : ℝ) / d)
  have hd : (0 : ℝ) < d := by exact_mod_cast h
  have h₂ : (⌈(x : ℝ) / d⌉ : ℝ) * d < x + d := by
    have := mul_lt_mul_of_pos_right h₁ hd
    rwa [add_mul, div_mul_cancel₀ _ hd.ne', one_mul] at this
  have h₃ : ⌈(x : ℝ) / d⌉ * d < x + d := by exact_mod_cast h₂
  exact Int.le_sub_one_of_lt h₃


-- created on 2019-10-01
