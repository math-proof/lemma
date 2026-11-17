module

public import Mathlib
public import Def.Data.List.Slice
public import Theorem.Nat.NotLt.is.Ge
public import Theorem.Nat.LeCoeS.is.Le
public import Theorem.Nat.CoeAdd.eq.AddCoeS
public import Theorem.Rat.CeilDivSub.eq.One.of.GeAdd.Gt_0
public import Theorem.Nat.LtCoeS.is.Lt
public import Theorem.Nat.LeSubS.of.Le
public import Theorem.Rat.DivSub.eq.SubDivS
public import Theorem.Rat.CeilSub_1.eq.SubCeil_1
public import Theorem.Int.Sub_Add.eq.SubSub
public import Theorem.Nat.Sub_Add.eq.SubSub
public import Theorem.Nat.Le.of.Sub.eq.Zero
public import Theorem.Nat.AddMul.eq.MulAdd_1
public import Theorem.Nat.EqSubAdd

public section

open Nat Int Rat


public theorem List.LengthSlicedIndices.eq.CeilDivSub.of.Gt_0.Le.Lt.Sub.le.Mul
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
