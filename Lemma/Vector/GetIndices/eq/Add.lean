import sympy.vector.vector
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Bool.OrOr.is.Or_Or
import Lemma.List.EqLengthSlice
import Lemma.List.GetSlicedIndices.eq.Add.of.Lt.LeAddS.Lt_Add
import Lemma.Int.EqToNat
open List Bool Int Nat


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
  have hi := i.isLt
  simp [EqLengthSlice] at hi
  split_ifs with h
  ·
    rw [AddCoeS.eq.CoeAdd] at h
    repeat rw [EqAdd_Mul_DivSub1Sign_2] at h
    simp at h
    rw [OrOr.is.Or_Or] at h
    rcases h with h | h | h <;> linarith
  ·
    simp [GetElem.getElem]
    simp [List.Vector.get]
    rw [← GetSlicedIndices.eq.Add.of.Lt.LeAddS.Lt_Add (show j < n + j by omega) (show n + j ≤ n + j by simp_all) (show i < n by simp_all)]
    congr
    .
      simp [EqAdd_Mul_DivSub1Sign_2]
    .
      rw [AddCoeS.eq.CoeAdd]
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
