import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Int.EqToNat
import Lemma.List.GetSlicedIndices.eq.AddMul.of.Gt_0.Gt_0.Lt.Lt
import Lemma.List.LengthSlicedIndices.eq.ToNatCeilDivSub.of.Gt_0.Le.Lt
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.CoeAdd_1.eq.AddCoe_1
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Gt_0
import Lemma.Nat.LeCoeS.is.Le
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Rat.EqCeilDivSubMul.of.Lt
import Lemma.Vector.EqGetS
import Lemma.List.EqLengthSlice_Mul.of.Lt
import sympy.core.relational
import sympy.vector.vector
open Bool Int List Nat Rat Vector


@[main]
private lemma main
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  (List.Vector.indices ⟨j, m * n, n⟩ (m * n)).get ⟨i, by simp [EqLengthSlice_Mul.of.Lt (j.isLt)]⟩ = ↑i * n + j := by
-- proof
  unfold List.Vector.indices Slice.toList
  simp
  have h_j := j.isLt
  have h_i := i.isLt
  have h_n := Gt_0 j
  have h_m := Gt_0 i
  split_ifs with h
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    contrapose! h
    constructor
    ·
      nlinarith
    ·
      apply Lt0Mul.of.Gt_0.Gt_0
      repeat omega
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    match n with
    | 0 =>
      contradiction
    | n + 1 =>
      denote h_start_eq : start = (Slice.Add_Mul_DivSub1Sign_2 (m * (n + 1)) j).toNat
      denote h_stop_eq : stop = (Slice.Add_Mul_DivSub1Sign_2 (m * (n + 1)) (↑m * (↑n + 1))).toNat.min (m * (n + 1))
      simp [← h_start_eq, ← h_stop_eq]
      rw [EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_start_eq
      rw [OfNat.eq.Cast (α := ℤ), @Nat.AddCoeS.eq.CoeAdd, MulCoeS.eq.CoeMul, EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_stop_eq
      simp at h_stop_eq
      denote h_step_eq : step = n.succ
      simp [h_start_eq, h_stop_eq]
      simp [EqGetS]
      apply GetSlicedIndices.eq.AddMul.of.Gt_0.Gt_0.Lt.Lt _ h_j
      repeat linarith


@[main]
private lemma Comm
-- given
  (i : Fin m)
  (j : Fin n) :
-- imply
  (List.Vector.indices ⟨j, n * m, n⟩ (n * m)).get ⟨i, by simp [EqLengthSlice_Mul.of.Lt.comm (j.isLt)]⟩ = ↑i * n + j := by
-- proof
  unfold List.Vector.indices Slice.toList
  simp
  have h_j := j.isLt
  have h_i := i.isLt
  have h_n := Gt_0 j
  have h_m := Gt_0 i
  split_ifs with h
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    contrapose! h
    constructor
    ·
      nlinarith
    ·
      apply Lt0Mul.of.Gt_0.Gt_0
      repeat omega
  ·
    rw [MulCoeS.eq.CoeMul] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqToNat] at h
    rw [LeCoeS.is.Le] at h
    rw [Or.comm] at h
    rw [Or_Or.is.OrOr] at h
    simp at h
    match n with
    | 0 =>
      contradiction
    | n + 1 =>
      denote h_start_eq : start = (Slice.Add_Mul_DivSub1Sign_2 ((n + 1) * m) j).toNat
      denote h_stop_eq : stop = (Slice.Add_Mul_DivSub1Sign_2 ((n + 1) * m) ((↑n + 1) * ↑m)).toNat.min ((n + 1) * m)
      simp [← h_start_eq, ← h_stop_eq]
      rw [EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_start_eq
      rw [OfNat.eq.Cast (α := ℤ), @Nat.AddCoeS.eq.CoeAdd, MulCoeS.eq.CoeMul, EqAdd_Mul_DivSub1Sign_2, EqToNat] at h_stop_eq
      simp at h_stop_eq
      denote h_step_eq : step = n.succ
      simp [h_start_eq, h_stop_eq]
      simp [EqGetS]
      apply GetSlicedIndices.eq.AddMul.of.Gt_0.Gt_0.Lt.Lt.comm _ h_j
      repeat linarith


-- created on 2025-11-07
-- updated on 2025-11-08
