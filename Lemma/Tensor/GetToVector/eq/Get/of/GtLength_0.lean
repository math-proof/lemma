import sympy.tensor.stack
import Lemma.Algebra.LtVal
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetToVector.eq.Get
open Algebra Tensor List


@[main]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have hi := LtVal i
  X.toVector.get ⟨i, by rwa [HeadD.eq.Get_0.of.GtLength_0 h 1]⟩ = X.get ⟨i, by rwa [Length.eq.Get_0.of.GtLength_0 h]⟩ :=
-- proof
  GetToVector.eq.Get.fin X ⟨i, by simp [Length.eq.Get_0.of.GtLength_0 h X]⟩


@[main]
private lemma headD
-- given
  (h : s.length > 0)
  (X : Tensor α s)
  (i : Fin (s.headD 1)) :
-- imply
  X.toVector.get i = X.get ⟨i, by
    have hi := LtVal i
    simp only [HeadD.eq.Get_0.of.GtLength_0 h 1] at hi
    rwa [Length.eq.Get_0.of.GtLength_0 h]⟩ := by
-- proof
  have hi := LtVal i
  simp only [HeadD.eq.Get_0.of.GtLength_0 h 1] at hi
  apply main h X ⟨i, hi⟩


-- created on 2025-10-06
