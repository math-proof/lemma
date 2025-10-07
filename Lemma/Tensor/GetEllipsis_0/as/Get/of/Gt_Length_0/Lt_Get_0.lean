import stdlib.SEq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.tensor
import Lemma.Bool.SEqCast.of.Eq
open Tensor Bool


@[main]
private lemma main
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  X.getEllipsis ⟨0, h_s⟩ ⟨i, by simp_all⟩ ≃ X.get ⟨i, by simpa [Length.eq.Get_0.of.GtLength_0 h_s]⟩ := by
-- proof
  unfold Tensor.getEllipsis
  apply SEqCast.of.Eq
  simp


-- created on 2025-10-05
