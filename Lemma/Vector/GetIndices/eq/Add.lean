import sympy.vector.vector
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.Algebra.LtVal
import Lemma.List.EqLengthSlice
import Lemma.List.GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_Add.Eq
import Lemma.Int.EqToNat
open Algebra List Bool Int


@[main]
private lemma main
-- given
  (j n : ℕ)
  (i : Fin _) :
-- imply
  (List.Vector.indices ⟨j, n + j, 1⟩ (n + j))[i] = (i : ℕ) + j := by
-- proof
  unfold List.Vector.indices
  unfold Slice.toList
  simp
  split_ifs with h
  ·
    rw [AddCoeS.eq.CoeAdd.nat] at h
    rw [EqAdd_Mul_DivSub1Sign_2] at h
    rw [EqAdd_Mul_DivSub1Sign_2] at h
    simp at h
    rw [OrOr.is.Or_Or] at h
    have hi := LtVal i
    simp [EqLengthSlice] at hi
    rcases h with h | h | h <;> linarith
  ·
    simp [GetElem.getElem]
    simp [List.Vector.get]
    apply GetSlicedIndices.eq.Add.of.Lt_Length.Gt_0.Le.Lt.Eq_Add.Eq (n' := n)
    ·
      rw [EqAdd_Mul_DivSub1Sign_2]
      simp
    ·
      rw [AddCoeS.eq.CoeAdd.nat]
      rw [EqAdd_Mul_DivSub1Sign_2]
      simp only [EqToNat]
      simp


@[main]
private lemma coe
-- given
  (j n : ℕ)
  (i : Fin _) :
-- imply
  (List.Vector.indices ⟨j, (n + j : ℕ), 1⟩ (n + j))[i] = (i : ℕ) + j :=
-- proof
  main j n i


-- created on 2025-05-23
-- updated on 2025-05-24
