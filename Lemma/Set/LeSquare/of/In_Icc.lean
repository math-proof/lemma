import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x m M : ℝ}
-- given
  (h : x ∈ Set.Icc m M) :
-- imply
  x * x ≤ max (m * m) (M * M) := by
-- proof
  if hx : 0 ≤ x then
    apply le_trans (mul_self_le_mul_self hx h.2) (le_max_right _ _)
  else
    push Not at hx
    have h₁ : (0:ℝ) ≤ -x := (neg_pos.mpr hx).le
    have h₂ : -x ≤ -m := neg_le_neg h.1
    have := mul_self_le_mul_self h₁ h₂
    rw [neg_mul_neg, neg_mul_neg] at this
    apply le_trans this (le_max_left _ _)


-- created on 2021-03-26
