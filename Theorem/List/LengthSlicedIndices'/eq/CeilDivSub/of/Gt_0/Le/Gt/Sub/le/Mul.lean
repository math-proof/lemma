module

public import Mathlib
public import Def.Data.List.List.Basic
public import Theorem.Rat.CeilDivSub.eq.One.of.GeAdd.Gt_0
public import Theorem.Nat.LtCoeS.is.Lt
public import Theorem.Nat.Le.of.Sub.eq.Zero
public import Theorem.Nat.LeSubS.of.Le
public import Theorem.Nat.AddMul.eq.MulAdd_1
public import Theorem.Nat.NotLt.is.Ge
public import Theorem.Nat.LeCoeS.is.Le
public import Theorem.Nat.EqSubAdd
public import Theorem.Int.SubSub
public import Theorem.Nat.SubSub
public import Theorem.Nat.CoeSub.eq.SubCoeS.of.Gt
public import Theorem.Nat.Gt.of.GtSub
public import Theorem.Rat.DivSub.eq.SubDivS
public import Theorem.Rat.CeilSub_1.eq.SubCeil_1
public import Theorem.Nat.LeSub.is.Le_Add
public import Theorem.Nat.CoeAdd.eq.AddCoeS

public section

open Nat Int Rat Matrix


public theorem List.LengthSlicedIndices'.eq.CeilDivSub.of.Gt_0.Le.Gt.Sub.le.Mul
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
      have h' := LeSubS.of.Le h step
      rw [MulAdd_1.eq.AddMul] at h'
      rw [Nat.SubSub.Comm] at h'
      rw [EqSubAdd] at h'
      have h_Eq := ih h' h_start'
      rw [h_Eq]
      have h_Gt := Gt.of.GtSub h_start'
      rw [CoeSub.eq.SubCoeS.of.Gt h_Gt]
      rw [Int.SubSub.Comm]
      rw [DivSub.eq.SubDivS]
      rw [Div.eq.One.of.Gt_0 (by simp [h_step])]
      rw [CeilSub_1.eq.SubCeil_1]
      simp
    ·
      simp
      apply Eq.symm
      have h_Ge := Ge.of.NotLt h_start'
      have h_Ge := GeAdd.of.Ge_Sub h_Ge
      have h_Ge := GeCoeS.of.Ge (R := ℚ) h_Ge
      rw [CoeAdd.eq.AddCoeS] at h_Ge
      have h_stop := LtCoeS.of.Lt (R := ℚ) h_stop
      apply CeilDivSub.eq.One.of.GeAdd.Gt_0 (by apply GtCoeS.of.Gt h_step) h_Ge h_stop


-- created on 2025-05-04
-- updated on 2026-10-26
