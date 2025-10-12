import stdlib.List
import Lemma.Algebra.CeilDivSub.eq.One.of.GeAdd.Gt_0
import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Algebra.LtCoeS.is.Lt
import Lemma.Algebra.Le.of.Sub.eq.Zero
import Lemma.Algebra.LeSubS.of.Le
import Lemma.Algebra.AddMul.eq.MulAdd_1
import Lemma.Nat.Ge.of.NotLt
import Lemma.Algebra.GeCoeS.is.Ge
import Lemma.Nat.EqSubAdd
import Lemma.Int.SubSub
import Lemma.Nat.SubSub
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Algebra.Gt.of.GtSub
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.CeilSub_1.eq.SubCeil_1
import Lemma.Algebra.GeAdd.of.Ge_Sub
import Lemma.Nat.CoeAdd.eq.AddCoeS
open Algebra Nat Int


@[main]
private lemma main
-- given
  (h : start - stop ≤ k * step)
  (h_stop : start > stop)
  (h_start : start ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices' h_stop h_start h_step).length = ⌈(start - stop : ℚ) / step⌉ := by
-- proof
  induction k generalizing start with
  | zero =>
    simp at h
    have h := Le.of.Sub.eq.Zero h
    linarith
  | succ k ih =>
    unfold Nat.sliced_indices'
    simp
    split_ifs with h_start'
    ·
      have h' := LeSubS.of.Le.nat h step
      rw [MulAdd_1.eq.AddMul] at h'
      rw [Nat.SubSub.comm] at h'
      rw [EqSubAdd] at h'
      have h_Eq := ih h' h_start'
      rw [h_Eq]
      have h_Gt := Gt.of.GtSub h_start'
      rw [CoeSub.eq.SubCoeS.of.Gt h_Gt]
      rw [Int.SubSub.comm]
      rw [DivSub.eq.SubDivS]
      rw [Div.eq.One.of.Gt_0 (by simp [h_step])]
      rw [CeilSub_1.eq.SubCeil_1]
      simp
    ·
      simp
      apply Eq.symm
      have h_Ge := Ge.of.NotLt h_start'
      have h_Ge := GeAdd.of.Ge_Sub.nat h_Ge
      have h_Ge := GeCoeS.of.Ge.nat (R := ℚ) h_Ge
      rw [CoeAdd.eq.AddCoeS] at h_Ge
      have h_stop := LtCoeS.of.Lt.nat (R := ℚ) h_stop
      apply CeilDivSub.eq.One.of.GeAdd.Gt_0 (by apply GtCoeS.of.Gt.nat h_step) h_Ge h_stop


-- created on 2025-05-04
-- updated on 2025-05-05
