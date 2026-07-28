import Lemma.Tensor.EqData0'0
import sympy.tensor.tensor
import Lemma.Vector.EqGet0_0
open Tensor Vector


@[main]
private lemma main
  [LE α] [Zero α]
  {A : Tensor α s}
-- given
  (h_pos : A ≥ 0)
  (k : Fin s.prod) :
-- imply
  A.data[k] ≥ 0 := by
-- proof
  have h' := h_pos k
  dsimp [LE.le, GetElem.getElem] at h'
  rw [EqData0'0] at h'
  rwa [EqGet0_0.fin] at h'


-- created on 2026-07-27
