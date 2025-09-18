import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEqBFnSGet.of.SEq.GtLength_0
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : s.length > 0)
  (h_X : X ≃ X')
  (i : Fin s[0])
  (dim : ℕ) :
-- imply
  have : i < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp
  have h_s := h_X.left
  have : i < X'.length := by
    rw [h_s] at h
    rw [Length.eq.Get_0.of.GtLength_0 h]
    simp [← h_s]
  X[i].sum dim ≃ X'[i].sum dim := by
-- proof
  apply SEqBFnSGet.of.SEq.GtLength_0 h h_X i _ (fun s X => X.sum dim)


-- created on 2025-07-13
