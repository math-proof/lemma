import stdlib.Slice
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.GeCoeS.is.Ge
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Rat.CeilDivSub.eq.One.of.GeAdd.Gt_0
import Lemma.Nat.GtCoeS.is.Gt
import Lemma.Nat.LeSubS.of.Le
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Rat.CeilSub_1.eq.SubCeil_1
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Algebra.Le.of.Sub.eq.Zero
import Lemma.Nat.AddMul.eq.MulAdd_1
import Lemma.Nat.EqSubAdd
open Algebra Nat Int Rat


@[main]
private lemma main
-- given
  (h : stop - start ≤ k * step)
  (h_start : start < stop)
  (h_stop : stop ≤ n)
  (h_step : step > 0) :
-- imply
  (Nat.sliced_indices h_start h_stop h_step).length = ⌈(stop - start : ℚ) / step⌉ := by
-- proof
  induction k generalizing start with
  | zero =>
    simp at h
    have h := Le.of.Sub.eq.Zero h
    linarith
  | succ k ih =>
    unfold Nat.sliced_indices
    simp
    split_ifs with h_start'
    ·
      have h' := LeSubS.of.Le h step
      rw [MulAdd_1.eq.AddMul] at h'
      rw [@Nat.SubSub.eq.Sub_Add] at h'
      rw [EqSubAdd] at h'
      have h_Eq := ih h' h_start'
      rw [h_Eq]
      rw [CoeAdd.eq.AddCoeS]
      rw [@Int.Sub_Add.eq.SubSub]
      rw [DivSub.eq.SubDivS]
      rw [Div.eq.One.of.Gt_0 (by simp [h_step])]
      rw [CeilSub_1.eq.SubCeil_1]
      simp
    ·
      simp
      apply Eq.symm
      have h_Ge := Ge.of.NotLt h_start'
      have h_Ge := GeCoeS.of.Ge (R := ℚ) h_Ge
      rw [CoeAdd.eq.AddCoeS] at h_Ge
      apply CeilDivSub.eq.One.of.GeAdd.Gt_0 (by apply GtCoeS.of.Gt h_step) h_Ge (by apply GtCoeS.of.Gt h_start)


-- created on 2025-05-04
