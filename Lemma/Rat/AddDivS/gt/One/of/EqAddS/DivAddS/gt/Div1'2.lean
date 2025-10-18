import Lemma.Nat.Mul2.eq.Add
import Lemma.Nat.Add
import Lemma.Nat.Mul
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Rat.DivDiv.eq.Div_Mul
import Lemma.Algebra.GtMulS.of.Gt.Gt_0
import Lemma.Rat.DivAdd.eq.AddDivS
open Algebra Rat Nat


@[main]
private lemma main
-- α is a linear ordered field, e.g. ℝ or ℚ
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- TP denotes true positive
-- FP denotes false positive
-- TN denotes true negative
-- FN denotes false negative
  {TP FP TN FN : α}
-- given
-- the sum of Positive equals the sum of Negative
  (h₀ : TP + FP = TN + FN)
  (h₁ : (TP + TN) / (TP + FP + TN + FN) > 1 / 2) :
-- imply
  TP / (TP + FP) + TN / (TN + FN) > 1 := by
-- proof
  rw [h₀] at h₁
  rw [Add.comm (a := TN)] at h₁
  rw [AddAdd.eq.Add_Add (a := FN) (b := TN)] at h₁
  simp only [Add.eq.Mul2] at h₁
  rw [AddAdd.comm] at h₁
  simp only [Add.eq.Mul2] at h₁
  rw [AddMulS.eq.Mul_Add] at h₁
  rw [Mul.comm] at h₁
  rw [Div_Mul.eq.DivDiv] at h₁
  have h₁ := GtMulS.of.Gt.Gt_0 h₁ (by norm_num : (2 : α) > 0)
  simp at h₁
  rw [h₀]
  rw [AddDivS.eq.DivAdd]
  rwa [Add.comm (a := TN)]


-- created on 2024-11-28
