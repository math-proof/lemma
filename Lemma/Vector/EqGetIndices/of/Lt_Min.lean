import sympy.vector.vector
import Lemma.List.LengthSlice.eq.Min
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.List.GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_0
open Algebra List


@[main]
private lemma main
  {i n m : ℕ}
-- given
  (h : i < n ⊓ m) :
-- imply
  have : i < (List.Vector.indices ⟨0, n, 1⟩ m).length := by simp_all [LengthSlice.eq.Min]
  (List.Vector.indices ⟨0, n, 1⟩ m)[i] = i := by
-- proof
  unfold List.Vector.indices
  simp [GetElem.getElem]
  simp [List.Vector.get]
  simp [Slice.toList]
  split_ifs with h
  ·
    simp [EqAdd_Mul_DivSub1Sign_2] at h
    simp [EqAdd_Mul_DivSub1Sign_2.zero] at h
    omega
  ·
    apply GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_0
    simp [EqAdd_Mul_DivSub1Sign_2.zero]


@[main]
private lemma fin
  {i n m : ℕ}
-- given
  (h : i < n ⊓ m) :
-- imply
  have h_i : i < (List.Vector.indices ⟨0, n, 1⟩ m).length := by simp_all [LengthSlice.eq.Min]
  (List.Vector.indices ⟨0, n, 1⟩ m).get ⟨i, h_i⟩ = i := by
-- proof
  apply main
  repeat assumption


-- created on 2025-08-04
