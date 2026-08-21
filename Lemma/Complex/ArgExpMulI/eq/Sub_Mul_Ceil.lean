import Lemma.Int.Floor.eq.NegCeilNeg
import sympy.core.numbers
import sympy.functions.elementary.complexes
open Int


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  arg ((I * x).exp) = x - 2 * π * ⌈x / (2 * π) - 1 / 2⌉ := by
-- proof
  rw [mul_comm I (x : ℂ), Complex.exp_mul_I]
  have h := Complex.arg_cos_add_sin_mul_I_sub x
  have h_neg : -((π - x) / (2 * π)) = x / (2 * π) - 1 / 2 := by
    field_simp
    ring
  rw [Floor.eq.NegCeilNeg, h_neg, Int.cast_neg] at h
  linarith


-- created on 2018-08-25
-- updated on 2026-08-21
