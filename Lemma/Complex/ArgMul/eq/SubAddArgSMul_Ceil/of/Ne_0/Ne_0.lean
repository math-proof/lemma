import sympy.core.numbers
import Lemma.Algebra.EqArg.of.Gt_0
import Lemma.Complex.ArgExpMulI.eq.Sub_Mul_Ceil
open Algebra Complex


@[main]
private lemma main
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0) :
-- imply
  arg (x * y) = arg x + arg y - 2 * π * ⌈(arg x + arg y) / (2 * π) - 1 / 2⌉ := by
-- proof
  have h_abs : ‖x‖ * ‖y‖ > 0 :=
    mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  have hxy : x * y = ↑(‖x‖ * ‖y‖) * (I * (arg x + arg y)).exp := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I x, ← norm_mul_exp_arg_mul_I y]
    rw [mul_comm (arg x : ℂ) I, mul_comm (arg y : ℂ) I]
    calc
      ↑‖x‖ * (I * arg x).exp * (↑‖y‖ * (I * arg y).exp)
          = ↑‖x‖ * ↑‖y‖ * ((I * arg x).exp * (I * arg y).exp) := by
        ring
      _ = ↑(‖x‖ * ‖y‖) * ((I * arg x).exp * (I * arg y).exp) := by
        rw [ofReal_mul]
      _ = ↑(‖x‖ * ‖y‖) * (I * (arg x + arg y)).exp := by
        rw [← exp_add]
        have h_add : I * arg x + I * arg y = I * (arg x + arg y) := by
          rw [← mul_add, ← ofReal_add]
        rw [h_add]
  rw [hxy, EqArg.of.Gt_0 h_abs]
  rw [← ofReal_add]
  apply ArgExpMulI.eq.Sub_Mul_Ceil


-- created on 2018-10-25
-- updated on 2026-08-20
