import Lemma.Algebra.Sub.lt.Zero.of.Lt
import Lemma.Algebra.AddSub.eq.Sub_Sub
import Lemma.Int.SubSub
import Lemma.Algebra.Mul_Sub.eq.SubMulS
import Lemma.Algebra.SubCubeS.eq.MulSub__AddSquareS
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Algebra.Lt.of.Sub.lt.Zero
import Lemma.Algebra.Lt_0.of.Mul.lt.Zero.Gt_0
import Lemma.Set.AddAddSquareS.lt.Div3'4.of.In_Ico0.In_Ico0
import Lemma.Algebra.LtMulS.of.Gt_0.Lt
import Lemma.Algebra.Sub.gt.Zero.is.Lt
open Algebra Set Nat Int


def f (x : ℝ) := 3 * x - 4 * x ^ 3


/--
This lemma establishes that the function \( f(x) = 3x - 4x^3 \) is strictly increasing on the interval \([0, \frac{1}{2})\). Consequently, for any \( x_0, x_1 \) within this interval, if \( f(x_0) < f(x_1) \), then it must follow that \( x_0 < x_1 \). The proof leverages the positivity of the derivative \( f'(x) = 3 - 12x^2 \) over \([0, \frac{1}{2})\) to confirm the function's monotonicity.
-/
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
  -- show that f x is strictly increasing at interval (0, 1 / 2) since y' = 3 - 12 * x² = 3 * (1 - 2 * x) * (1 + 2 * x) > 0 for x ∈ [0, 1/2), thus proving the main lemma
  -- suppose f is defined as:
  -- def f (x : ℝ) := 3 * x  - 4 * x ^ 3
  have h_f0 : f x₀ = 3 * x₀ - 4 * x₀ ^ 3 := rfl
  have h_f1 : f x₁ = 3 * x₁ - 4 * x₁ ^ 3 := rfl
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
