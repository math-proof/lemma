import Lemma.Int.Floor.eq.NegCeilNeg
import Lemma.Complex.ExpMulI.eq.AddCos_MulISin
open Int Complex


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  arg ((I * x).exp) = x - 2 * π * ⌈x / (2 * π) - 1 / 2⌉ := by
-- proof
  rw [ExpMulI.eq.AddCos_MulISin, mul_comm I]
  have h := arg_cos_add_sin_mul_I_sub x
  have h_neg : -((π - x) / (2 * π)) = x / (2 * π) - 1 / 2 := by
    field_simp
    ring
  rw [Floor.eq.NegCeilNeg, h_neg, Int.cast_neg] at h
  linarith


-- created on 2018-08-25
-- updated on 2026-08-21
