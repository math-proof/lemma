import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Algebra.Gt.of.Lt
import Lemma.Set.Lt.of.LtUFn.In_Ico.In_Ico
import Lemma.Algebra.Lt_Sqrt.is.LtSquare.of.Ge_0
open Algebra Set Rat


/--
**Lemma:** Let \( x \) be a real number in the interval \([0, \frac{1}{2})\) that satisfies the equation \( 3x - 4x^3 = \frac{\sqrt{3}}{2} \). Then \( x > \frac{1}{3} \).

**Explanation:** This lemma establishes that within the interval \([0, \frac{1}{2})\), the solution to the equation \( 3x - 4x^3 = \frac{\sqrt{3}}{2} \) must lie strictly greater than \(\frac{1}{3}\). The proof leverages the monotonicity of the function \( f(x) = 3x - 4x^3 \) on the interval, demonstrating that since \( f \) is strictly increasing and \( f(\frac{1}{3}) < \frac{\sqrt{3}}{2} \), the solution \( x \) must exceed \(\frac{1}{3}\) to satisfy the equation.
-/
@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 ((1 : ℝ) / 2))
  (h₁ : 3 * x - 4 * x ^ 3 = √3 / 2) :
-- imply
  x > 1 / 3 := by
-- proof
  -- suppose f is defined as:
  -- def f (x : ℝ) := 3 * x  - 4 * x ^ 3
  have h_f_one_third : f (1 / 3) = 23 / 27 := by
    unfold f
    norm_num
  have : (46 : ℝ) / 27 < √3 := by
    rw [Lt_Sqrt.is.LtSquare.of.Ge_0]
    repeat norm_num
  have h_Lt := LtDivS.of.Lt.Gt_0 this (by norm_num : (2 : ℝ) > 0)
  norm_num at h_Lt
  rw [← h_f_one_third] at h_Lt
  have h_f : f x = 3 * x - 4 * x ^ 3 := rfl
  rw [← h_f] at h₁
  rw [← h₁] at h_Lt
  have h_Gt := Gt.of.Lt h_Lt
  have h_Mem : 1 / 3 ∈ Ico 0 ((1 : ℝ) / 2) := by norm_num
  -- show that f x is strictly increasing at interval (0, 1 / 2) since y' = 3 - 12 * x² > 0 for x ∈ [0, 1/2), thus proving the main lemma
  apply Lt.of.LtUFn.In_Ico.In_Ico h_Mem h₀ h_Gt


-- created on 2025-03-24
-- updated on 2025-03-25
