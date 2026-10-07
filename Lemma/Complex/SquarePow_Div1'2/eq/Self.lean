import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
-- given
  (z : ℂ) :
-- imply
  (z ^ (1 / 2 : ℂ)) ^ 2 = z := by
-- proof
  rw [one_div]
  exact_mod_cast Complex.cpow_ofNat_inv_pow z 2


-- created on 2026-10-07
