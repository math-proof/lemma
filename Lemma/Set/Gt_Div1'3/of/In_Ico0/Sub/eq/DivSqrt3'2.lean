import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Nat.Gt.of.Lt
import Lemma.Set.Lt.of.LtUFn.In_Ico.In_Ico
import Lemma.Real.Lt_Sqrt.is.LtSquare.of.Ge_0
open Set Rat Nat Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₀ : x ∈ Ico 0 ((1 : ℝ) / 2))
  (h₁ : 3 * x - 4 * x³ = √3 / 2) :
-- imply
  x > 1 / 3 := by
-- proof
  have h_f_one_third : f (1 / 3) = 23 / 27 := by
    unfold f
    norm_num
  have : (46 : ℝ) / 27 < √3 := by
    rw [Lt_Sqrt.is.LtSquare.of.Ge_0]
    repeat norm_num
  have h_Lt := LtDivS.of.Lt.Gt_0 this (by norm_num : (2 : ℝ) > 0)
  norm_num at h_Lt
  rw [← h_f_one_third] at h_Lt
  have h_f : f x = 3 * x - 4 * x³ := rfl
  rw [← h_f] at h₁
  rw [← h₁] at h_Lt
  have h_Gt := Gt.of.Lt h_Lt
  have h_Mem : 1 / 3 ∈ Ico 0 ((1 : ℝ) / 2) := by norm_num
  apply Lt.of.LtUFn.In_Ico.In_Ico h_Mem h₀ h_Gt


-- created on 2025-03-24
-- updated on 2025-03-25
