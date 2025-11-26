import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Tensor.SEqBFnSGet.of.SEq.GtLength_0
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {X' : Tensor α s'}
-- given
  (h : s.length > 0)
  (h_X : X ≃ X')
  (i : Fin s[0])
  (dim : ℕ) :
-- imply
  have h_s := h_X.left
  have := GtLength.of.GtLength_0 h X i
  have := GtLength.of.GtLength_0 (by grind) X' ⟨i, by grind⟩
  X[i].unsqueeze dim ≃ X'[i].unsqueeze dim := by
-- proof
  apply SEqBFnSGet.of.SEq.GtLength_0 h h_X i _ (fun s X => X.unsqueeze dim)


-- created on 2025-07-13
