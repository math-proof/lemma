import sympy.vector.vector
import Lemma.List.LengthSlice.eq.Min
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.List.EqGetSlicedIndices.of.Lt.Le.Gt_0
open List Nat


@[main, fin]
private lemma main
  {i n m : ℕ}
-- given
  (h : i < n ⊓ m) :
-- imply
  (List.Vector.indices ⟨0, n, 1⟩ m)[i]'(by simp_all [LengthSlice.eq.Min]) = i := by
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


-- created on 2025-08-04
