import sympy.functions.elementary.complexes
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Pow_3.eq.One |
| comm | Complex.One.eq.Pow_3 |
-/
@[main, comm]
private lemma main :
-- imply
  let ω := (I * (2 * π / 3)).exp
  ω ^ 3 = 1 := by
-- proof
  extract_lets ω
  simp only [ω]
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  ring


-- created on 2026-08-31
