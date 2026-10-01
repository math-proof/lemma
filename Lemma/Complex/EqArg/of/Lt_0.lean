import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {r : ℝ}
  {z : ℂ}
-- given
  (h : r < 0) :
-- imply
  arg (r * z) = arg (-z) := by
-- proof
  have e : (r : ℂ) * z = ((-r : ℝ) : ℂ) * (-z) := by push_cast; ring
  rw [e, Complex.arg_real_mul _ (by linarith)]


-- created on 2020-01-18
