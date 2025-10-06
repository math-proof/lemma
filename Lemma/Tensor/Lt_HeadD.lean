import sympy.tensor.Basic
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0
open Tensor List


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (i : Fin X.length)
  (default : ℕ := 1) :
-- imply
  i < s.headD default := by
-- proof
  have h_length := GtLength_0 i
  rw [HeadD.eq.Get_0.of.GtLength_0 h_length]
  rw [← Length.eq.Get_0.of.GtLength_0 h_length X]
  simp


-- created on 2025-10-06
