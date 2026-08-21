import sympy.Basic
import sympy.core.power
import sympy.core.numbers
import sympy.polys.polyroots
import sympy.functions.elementary.trigonometric


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : 0 ≤ x) :
-- imply
  arcsin x + arcsin (√(1 - x²)) = π / 2 := calc
-- proof
  _ = arccos (√(1 - x²)) + arcsin (√(1 - x²)) := by
    rw [Real.arcsin_eq_arccos h]
    rfl
  _ = π / 2 := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    ring


-- created on 2018-07-09
