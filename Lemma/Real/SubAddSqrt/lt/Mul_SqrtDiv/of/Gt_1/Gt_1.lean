import Lemma.Nat.MulMul
import Lemma.Int.Lt.of.LtSquareS.Ge_0
import Lemma.Int.Mul.ge.Zero.of.Ge_0.Ge_0
import Lemma.Real.GeSqrt_0
import Lemma.Nat.SquareMul.eq.MulSquareS
import Lemma.Real.EqSquareSqrt.of.Ge_0
import Lemma.Rat.Div.ge.Zero.of.Ge_0.Gt_0
import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Rat.DivMul.eq.MulDiv
import Lemma.Rat.EqDivSquare
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Int.Sub.gt.Zero.is.Lt
import Lemma.Int.AddSub.eq.SubAdd
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Int.SubMul.eq.MulSub_1
import Lemma.Int.SubSub
import Lemma.Int.AddSub.eq.Add_Sub
import Lemma.Int.MulSub.eq.SubMulS
import Lemma.Nat.Square.eq.Mul
import Lemma.Nat.Mul
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Int.EqSub_Sub
import Lemma.Nat.Mul.gt.Zero.of.Gt_0.Gt_0
import Lemma.Real.AddSub_Mul2Sqrt.gt.Zero.of.Gt_1
open Nat Int Real Rat


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
      repeat rw [Sub_Add.eq.SubSub]
      rw [SubMul.eq.MulSub_1]
      rw [SubSub.comm]
      rw [AddSub.eq.Add_Sub]
      rw [Square.eq.Mul]
      rw [@Int.SubMulS.eq.MulSub]
      rw [EqSub_Sub]
      rw [Mul.comm]
      rw [MulMul]
      rw [@Int.SubMulS.eq.MulSub]
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
