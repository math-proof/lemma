import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Algebra.Gt.of.Lt
import Lemma.Set.Lt.of.LtUFn.In_Ico.In_Ico
open Algebra Set Rat


/--
Given \( x \in [0, \frac{1}{2}) \) satisfying \( 3x - 4x^3 = \frac{\sqrt{3}}{2} \), this lemma proves \( x < \frac{7}{20} \).
The proof leverages the strict monotonicity of the function \( f(x) = 3x - 4x^3 \) on the interval, showing that \( f\left(\frac{7}{20}\right) > \frac{\sqrt{3}}{2} \), thus the solution must lie to the left of \( \frac{7}{20} \).
-/
@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 (1 / 2))
  (h₁ : 3 * x - 4 * x ^ 3 = √3 / 2) :
-- imply
  x < 7 / 20 := by
-- proof
  have h_f_frac_7_20 : f (7 / 20) = 1757 / 2000 := by
    unfold f
    norm_num
  -- try to show that √3/2 < 1757 / 2000
  have : Real.sqrt 3 < (1757 : ℝ) / 1000 := by
    rw [Real.sqrt_lt]
    repeat norm_num
  have h_Lt := LtDivS.of.Lt.Gt_0 this (by norm_num : (2 : ℝ) > 0)
  norm_num at h_Lt
  rw [← h_f_frac_7_20] at h_Lt
  have h_f : f x = 3 * x - 4 * x ^ 3 := rfl
  rw [← h_f] at h₁
  rw [← h₁] at h_Lt
  have h_Gt := Gt.of.Lt h_Lt
  have h_Mem : 7 / 20 ∈ Ico 0 ((1 : ℝ) / 2) := by norm_num
  -- show that f x is strictly increasing at interval (0, 1 / 2) since y' = 3 - 12 * x² > 0 for x ∈ [0, 1/2), thus proving the main lemma
  apply Lt.of.LtUFn.In_Ico.In_Ico h₀ h_Mem h_Gt


-- created on 2025-03-24
-- updated on 2025-04-05
