import stdlib.SEq
import sympy.tensor.functions
import Lemma.Tensor.GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq
import Lemma.Logic.SEqCast.of.SEq.Eq
open Tensor Logic


@[main]
private lemma main
  [Add α] [Zero α]
  {s : List ℕ}
  {dim : Fin s.length}
-- given
  (h : s[dim] > 0)
  (X : Tensor α s) :
-- imply
  X.sum dim ≃ (X.sum_keepdim dim).getEllipsis dim ⟨0, h⟩ := by
-- proof
  unfold Tensor.sum_keepdim
  simp
  have h_dim : dim.val < ((s.eraseIdx dim.val).insertIdx dim.val 1).length := by
    sorry
  have h_s : s = (((s.eraseIdx ↑dim).insertIdx (↑dim) 1).set dim.val (s[dim.val] * ((s.eraseIdx dim.val).insertIdx dim.val 1)[dim.val])) := by
    simp
    sorry
  have h_dim' : ↑dim < (((s.eraseIdx ↑dim).insertIdx (↑dim) 1).set (↑dim) (s[↑dim] * ((s.eraseIdx ↑dim).insertIdx (↑dim) 1)[↑dim])).length := by
    simp
    sorry
  have h_0 : 0 < (((s.eraseIdx dim.val).insertIdx dim.val 1).set dim.val (s[dim.val] * ((s.eraseIdx dim.val).insertIdx dim.val 1)[↑dim]))[dim] := by
    sorry
  have h_cast := GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq h_s ((((X.sum ↑dim).unsqueeze ↑dim).repeat s[↑dim] ⟨↑dim, h_dim⟩)) ⟨dim, h_dim'⟩ ⟨0, h_0⟩
  simp at h_cast
  simp [h_cast]
  apply SEq_Cast.of.SEq.Eq
  ·
    simp
    sorry
  ·
    sorry


-- created on 2025-10-05
