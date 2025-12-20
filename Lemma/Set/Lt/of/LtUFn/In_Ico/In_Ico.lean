import Lemma.Int.Sub.lt.Zero.of.Lt
import Lemma.Int.AddSub.eq.Sub_Sub
import Lemma.Int.SubSub
import Lemma.Int.Mul_Sub.eq.SubMulS
import Lemma.Int.SubCubeS.eq.MulSub__AddSquareS
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Int.Lt.of.Sub.lt.Zero
import Lemma.Int.Lt_0.of.Mul.lt.Zero.Gt_0
import Lemma.Set.AddAddSquareS.lt.Div3'4.of.In_Ico0.In_Ico0
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Int.Sub.gt.Zero.is.Lt
open Set Nat Int


def f (x : ℝ) := 3 * x - 4 * x³


@[main]
private lemma main
  {x₀ x₁ : ℝ}
-- given
  (h₀ : x₀ ∈ Ico 0 (1 / 2))
  (h₁ : x₁ ∈ Ico 0 (1 / 2))
  (h₂ : f x₀ < f x₁) :
-- imply
  x₀ < x₁ := by
-- proof
  have h_f0 : f x₀ = 3 * x₀ - 4 * x₀³ := rfl
  have h_f1 : f x₁ = 3 * x₁ - 4 * x₁³ := rfl
  rw [h_f0, h_f1] at h₂
  have := Sub.lt.Zero.of.Lt h₂
  rw [Sub_Sub.eq.AddSub] at this
  rw [SubSub.comm] at this
  rw [SubMulS.eq.Mul_Sub] at this
  rw [AddSub.eq.Sub_Sub] at this
  rw [SubMulS.eq.Mul_Sub] at this
  rw [SubCubeS.eq.MulSub__AddSquareS] at this
  rw [Mul_Mul.eq.MulMul] at this
  rw [Mul.comm] at this
  rw [Mul.comm (a := 4)] at this
  rw [MulMul.eq.Mul_Mul] at this
  rw [SubMulS.eq.Mul_Sub] at this
  apply Lt.of.Sub.lt.Zero
  apply Lt_0.of.Mul.lt.Zero.Gt_0 this
  apply Sub.gt.Zero.of.Lt
  have := AddAddSquareS.lt.Div3'4.of.In_Ico0.In_Ico0 h₀ h₁
  have := LtMulS.of.Gt_0.Lt (by norm_num : 4 > (0 : ℝ)) this
  norm_num at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-05
