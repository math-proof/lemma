import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x m M : ℝ}
-- given
  (h : x ∈ Set.Ioo m M) :
-- imply
  x * x < max (m * m) (M * M) := by
-- proof
  if hx : 0 ≤ x then
    have hM : (0:ℝ) ≤ M := le_trans hx h.2.le
    apply lt_of_lt_of_le ((mul_self_lt_mul_self_iff hx hM).mp h.2) (le_max_right _ _)
  else
    push Not at hx
    have h₁ : (0:ℝ) ≤ -x := (neg_pos.mpr hx).le
    have h₂ : -x < -m := neg_lt_neg h.1
    have h₃ : (0:ℝ) ≤ -m := le_of_lt (lt_of_le_of_lt h₁ h₂)
    have := (mul_self_lt_mul_self_iff h₁ h₃).mp h₂
    rw [neg_mul_neg, neg_mul_neg] at this
    apply lt_of_lt_of_le this (le_max_left _ _)


-- created on 2019-08-31
