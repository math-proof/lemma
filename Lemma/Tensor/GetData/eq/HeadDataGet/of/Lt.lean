import Lemma.Tensor.GetData.eq.GetDataGet.of.Lt
import Lemma.Tensor.GtLength.of.GtLength_0
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector


@[main, fin]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α [n]) :
-- imply
  have := GtLength.of.GtLength_0 (by grind) X ⟨i, by grind⟩
  X.data[i]'(by simpa) = X[i].data.head := by
-- proof
  simp
  rw [Head.eq.Get_0.fin]
  apply GetData.eq.GetDataGet.of.Lt h_i


-- created on 2026-08-08
