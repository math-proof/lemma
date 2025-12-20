import sympy.core.power
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Nat.Gt.of.Lt
import Lemma.Set.Lt.of.LtUFn.In_Ico.In_Ico
open Set Rat Nat


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 (1 / 2))
  (h₁ : 3 * x - 4 * x³ = √3 / 2) :
-- imply
  x < 7 / 20 := by
-- proof
  have h_f_frac_7_20 : f (7 / 20) = 1757 / 2000 := by
    unfold f
    norm_num
  have : Real.sqrt 3 < (1757 : ℝ) / 1000 := by
    rw [Real.sqrt_lt]
    repeat norm_num
  have h_Lt := LtDivS.of.Lt.Gt_0 this (by norm_num : (2 : ℝ) > 0)
  norm_num at h_Lt
  rw [← h_f_frac_7_20] at h_Lt
  have h_f : f x = 3 * x - 4 * x³ := rfl
  rw [← h_f] at h₁
  rw [← h₁] at h_Lt
  have h_Gt := Gt.of.Lt h_Lt
  have h_Mem : 7 / 20 ∈ Ico 0 ((1 : ℝ) / 2) := by norm_num
  apply Lt.of.LtUFn.In_Ico.In_Ico h₀ h_Mem h_Gt


-- created on 2025-03-24
-- updated on 2025-04-05
