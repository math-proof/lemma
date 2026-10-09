import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
-- given
  (z : ℂ) :
-- imply
  (z ^ (1 / 3 : ℂ)) ^ 3 = z := by
-- proof
  rw [one_div]
  exact_mod_cast Complex.cpow_ofNat_inv_pow z 3


-- created on 2026-10-07
