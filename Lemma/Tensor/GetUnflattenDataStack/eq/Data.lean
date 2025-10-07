import sympy.tensor.stack
import Lemma.Vector.EqUnflattenFlatten
open Vector


@[main]
private lemma fin
-- given
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).data.unflatten[i] = (f i).data := by
-- proof
  unfold Stack Tensor.fromVector
  simp [← Eq_UnflattenFlatten]
  simp [GetElem.getElem]
  congr
  simp [List.Vector.get]
  simp [List.Vector.range]


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (i : Fin n) :
-- imply
  ([i < n] f i).data.unflatten[i] = (f i).data := by
-- proof
  apply fin


-- created on 2025-07-17
