import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Eq.of.All_EqDataSGetToVector
open Tensor


@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor α (m :: s)) :
-- imply
  A = B ↔ ∀ i : Fin m, A[i] = B[i] := by
-- proof
  constructor <;>
    intro h
  .
    aesop
  .
    simp [Eq.is.EqDataS (s := s)] at h
    simp [GetElem.getElem] at h
    simp [Tensor.get] at h
    have h_all : ∀ i : Fin m, A.toVector[i].data = B.toVector[i].data := by
      intro i
      have h_eq := h i
      have hi : i < A.length := by
        simp [Tensor.length]
      have hi : i < B.length := by
        simp [Tensor.length]
      assumption
    apply Eq.of.All_EqDataSGetToVector h_all


-- created on 2025-05-06
-- updated on 2025-05-18
