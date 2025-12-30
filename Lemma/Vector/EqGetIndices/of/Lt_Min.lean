import sympy.vector.vector
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.List.EqGetSlicedIndices.of.Lt.Le.Gt_0
open List Nat


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
    apply EqGetSlicedIndices.of.Lt.Le.Gt_0
    simp_all [EqAdd_Mul_DivSub1Sign_2]


@[main]
private lemma fin
  {i n m : ℕ}
-- given
  (h : i < n ⊓ m) :
-- imply
  have h_i : i < (List.Vector.indices ⟨0, n, 1⟩ m).length := by simp_all [LengthSlice.eq.Min]
  (List.Vector.indices ⟨0, n, 1⟩ m).get ⟨i, h_i⟩ = i :=
-- proof
  main h


-- created on 2025-08-04
