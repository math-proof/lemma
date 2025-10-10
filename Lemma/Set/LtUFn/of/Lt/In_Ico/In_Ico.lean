import Lemma.Algebra.Lt.of.Sub.lt.Zero
import Lemma.Algebra.AddSub.eq.Sub_Sub
import Lemma.Algebra.SubSub
import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Algebra.SubCubeS.eq.MulSub__AddSquareS
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Algebra.Sub.lt.Zero.of.Lt
import Lemma.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
import Lemma.Algebra.Sub.gt.Zero.is.Lt
import Lemma.Set.AddAddSquareS.lt.Div3'4.of.In_Ico0.In_Ico0
import Lemma.Algebra.LtMulS.of.Gt_0.Lt
open Algebra Set Nat


def f (x : ℝ) := 3 * x  - 4 * x ^ 3


@[main]
private lemma main
  {x₀ x₁ : ℝ}
-- given
  (h₀ : x₀ ∈ Ico 0 ((1 : ℝ) / 2))
  (h₁ : x₁ ∈ Ico 0 ((1 : ℝ) / 2))
  (h₂ : x₀ < x₁) :
-- imply
  f x₀ < f x₁ := by
-- proof
  -- show that f x is strictly increasing at interval (0, 1 / 2) since y' = 3 - 12 * x² = 3 * (1 - 2 * x) * (1 + 2 * x) > 0 for x ∈ [0, 1/2), thus proving the main lemma
  have h_f0 : f x₀ = 3 * x₀ - 4 * x₀ ^ 3 := rfl
  have h_f1 : f x₁ = 3 * x₁ - 4 * x₁ ^ 3 := rfl
  rw [h_f0, h_f1]
  apply Lt.of.Sub.lt.Zero
  rw [Sub_Sub.eq.AddSub]
  rw [SubSub.comm]
  rw [SubMulS.eq.Mul_Sub]
  rw [AddSub.eq.Sub_Sub]
  rw [SubMulS.eq.Mul_Sub]
  rw [SubCubeS.eq.MulSub__AddSquareS]
  rw [Mul_Mul.eq.MulMul]
  rw [Mul.comm]
  rw [Mul.comm (a := 4)]
  rw [MulMul.eq.Mul_Mul]
  rw [SubMulS.eq.Mul_Sub]
  have h_Lt_0 := Sub.lt.Zero.of.Lt h₂
  apply Mul.lt.Zero.of.Lt_0.Gt_0 h_Lt_0
  apply Sub.gt.Zero.of.Lt
  have := AddAddSquareS.lt.Div3'4.of.In_Ico0.In_Ico0 h₀ h₁
  have := LtMulS.of.Gt_0.Lt (by norm_num : 4 > (0 : ℝ)) this
  norm_num at this
  assumption


-- created on 2025-03-24
