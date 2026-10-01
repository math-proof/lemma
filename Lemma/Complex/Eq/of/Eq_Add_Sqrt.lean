import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma radical_Conjugate
  {x a d : ℂ}
-- given
  (h₀ : (x ^ 2 + d) ^ (1 / 2 : ℂ) - x = a)
  (h₁ : d ≠ 0) :
-- imply
  x = (d / a - a) / 2 := by
-- proof
  have hs : ((x ^ 2 + d) ^ (1 / 2 : ℂ)) ^ 2 = x ^ 2 + d := by
    have := Complex.cpow_ofNat_inv_pow (x ^ 2 + d) 2
    rw [one_div]
    exact_mod_cast this
  have hx : (x ^ 2 + d) ^ (1 / 2 : ℂ) = x + a := by rw [← h₀]; ring
  rw [hx] at hs
  have ha : a ≠ 0 := by
    rintro rfl
    apply h₁
    linear_combination -hs
  field_simp
  linear_combination hs


-- created on 2026-09-27
