import Lemma.Int.Lt.of.LtSquareS.Ge_0
import Lemma.Int.Le0Mul.of.Ge_0.Ge_0
import Lemma.Real.GeSqrt_0
import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Nat.SquareMul.eq.MulSquareS
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Rat.Div.ge.Zero.of.Ge_0.Gt_0
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivMul.eq.MulDiv
import Lemma.Int.LtAdd.of.Lt_Sub
import Lemma.Int.Sub.gt.Zero.is.Lt
import Lemma.Nat.Add
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Int.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Real.GtSqrtS.of.Gt.Gt_0
import Lemma.Int.GtSquare_0.of.Gt_0
import Lemma.Nat.Mul
import Lemma.Real.EqSquareSqrt.of.Gt_0
import Lemma.Int.AddSub.eq.SubAdd
import Lemma.Real.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
open Nat Int Rat Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 1) :
-- imply
  1 + √x < 2 * √((x + 1) / 2) := by
-- proof
  apply Lt.of.LtSquareS.Ge_0
  ·
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt.of.Ge_0]
    ·
      rw [SquareAdd.eq.AddAddSquareS_MulMul2]
      ring_nf
      rw [EqSquareSqrt.of.Ge_0 (by linarith)]
      repeat apply LtAdd.of.Lt_Sub
      ring_nf
      apply Lt.of.Sub.gt.Zero
      rw [Add.comm]
      rw [SubAdd.eq.Add_Sub]
      norm_num
      rw [Mul.comm]
      apply AddSub_Mul2Sqrt.gt.Zero.of.Gt_1 h
    ·
      apply Div.ge.Zero.of.Ge_0.Gt_0
      ·
        linarith [h]
      ·
        norm_num
  ·
    apply Le0Mul.of.Ge_0.Ge_0
    ·
      norm_num
    ·
      apply GeSqrt_0


-- created on 2025-04-06
