import sympy.core.numbers
import Lemma.Algebra.Expr.eq.MulAbs_ExpMulIArg
import Lemma.Algebra.EqArg.of.Gt_0
import Lemma.Complex.ArgExpMulI.eq.Sub_Mul_Ceil
open Algebra Complex


@[main]
private lemma main
  {z : ℂ}
  {n : ℕ}
-- given
  (hn : n > 0) :
-- imply
  arg (z ^ n) = n * arg z - 2 * π * ⌈n * arg z / (2 * π) - 1 / 2⌉ := by
-- proof
  by_cases hz : z = 0
  ·
    have hn' : n ≠ 0 := hn.ne'
    simp [hz, zero_pow hn', arg_zero]
    norm_num
  ·
    have hpos : (‖z‖ : ℝ) ^ n > 0 := pow_pos (norm_pos_iff.mpr hz) n
    have hzpow : z ^ n = ↑(‖z‖ ^ n) * (I * (n * arg z)).exp := by
      conv_lhs => rw [Algebra.Expr.eq.MulAbs_ExpMulIArg (z := z)]
      rw [mul_pow]
      have h_exp : (I * arg z).exp ^ n = (I * (n * arg z)).exp := by
        rw [← exp_nsmul]
        congr 1
        rw [nsmul_eq_mul]
        ring
      rw [h_exp, ofReal_pow]
    rw [hzpow, EqArg.of.Gt_0 hpos]
    have hcast : (↑n * ↑z.arg : ℂ) = ↑((n : ℝ) * z.arg) := (ofReal_mul (n : ℝ) z.arg).symm
    rw [hcast]
    apply ArgExpMulI.eq.Sub_Mul_Ceil


-- created on 2018-08-26
-- updated on 2026-08-20
