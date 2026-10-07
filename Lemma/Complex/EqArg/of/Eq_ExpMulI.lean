import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {z : ℂ}
-- given
  (h : z = Complex.exp (x * Complex.I)) :
-- imply
  x = arg z + ⌈x / (π * 2) - 1 / 2⌉ * π * 2 := by
-- proof
  rw [h, Complex.arg_exp_mul_I, toIocMod, toIocDiv_eq_neg_floor, zsmul_eq_mul]
  have hp : (0 : ℝ) < π := Real.pi_pos
  have e : (-π + 2 * π - x) / (2 * π) = -(x / (π * 2) - 1 / 2) := by field_simp; ring
  rw [e, Int.floor_neg]
  push_cast
  ring


-- created on 2019-04-22
