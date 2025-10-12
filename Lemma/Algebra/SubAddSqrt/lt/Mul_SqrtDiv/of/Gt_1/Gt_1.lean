import Lemma.Algebra.MulMul
import Lemma.Algebra.Lt.of.LtSquareS.Ge_0
import Lemma.Algebra.Mul.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.GeSqrt_0
import Lemma.Nat.SquareMul.eq.MulSquareS
import Lemma.Algebra.EqSquareSqrt.of.Ge_0
import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Gt_0
import Lemma.Algebra.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.DivMul.eq.MulDiv
import Lemma.Algebra.EqDivSquare
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Algebra.Sub.gt.Zero.is.Lt
import Lemma.Algebra.AddSub.eq.SubAdd
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Algebra.SubMul.eq.MulSub_1
import Lemma.Int.SubSub
import Lemma.Algebra.AddSub.eq.Add_Sub
import Lemma.Algebra.MulSub.eq.SubMulS
import Lemma.Algebra.Square.eq.Mul
import Lemma.Nat.Mul
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.EqSub_Sub
import Lemma.Algebra.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Algebra.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
open Algebra Nat Int


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
-- given
  (h₀ : n > 1)
  (h₁ : x > 1) :
-- imply
  √x + n - 1 < n * √((x + n - 1) / n) := by
-- proof
  apply Lt.of.LtSquareS.Ge_0
  ·
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt.of.Ge_0]
    ·
      rw [SubAdd.eq.Add_Sub]
      rw [SquareAdd.eq.AddAddSquareS_MulMul2]
      field_simp
      rw [EqSquareSqrt.of.Ge_0 (by linarith)]
      rw [SubAdd.eq.Add_Sub]
      rw [Mul_Add.eq.AddMulS]
      apply Lt.of.Sub.gt.Zero
      rw [SubAdd.eq.AddSub]
      rw [Sub_Add.eq.SubSub]
      rw [Sub_Add.eq.SubSub]
      rw [SubMul.eq.MulSub_1]
      rw [SubSub.comm]
      rw [AddSub.eq.Add_Sub]
      rw [Square.eq.Mul]
      rw [SubMulS.eq.MulSub]
      rw [EqSub_Sub]
      rw [Mul.comm]
      rw [MulMul]
      rw [SubMulS.eq.MulSub]
      rw [AddMulS.eq.MulAdd]
      apply Mul.gt.Zero.of.Gt_0.Gt_0
      ·
        apply AddSub_Mul2Sqrt.gt.Zero.of.Gt_1 h₁
      ·
        simp
        linarith [h₀]
    ·
      apply Div.ge.Zero.of.Ge_0.Gt_0
      ·
        linarith [h₀]
      ·
        norm_cast
        linarith [h₀]
  ·
    apply Mul.ge.Zero.of.Ge_0.Ge_0
    ·
      simp
    ·
      apply GeSqrt_0


-- created on 2025-04-06
