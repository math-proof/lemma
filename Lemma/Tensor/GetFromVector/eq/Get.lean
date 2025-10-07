import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetSplitAt_1.eq.GetUnflatten.of.Lt
import Lemma.Algebra.LtVal
import Lemma.Vector.EqUnflattenFlatten
open Vector Tensor Algebra Bool


@[main]
private lemma main
-- given
  (v : List.Vector (Tensor α s) n)
  (i : Fin n) :
-- imply
  (Tensor.fromVector v)[i] = v[i] := by
-- proof
  unfold Tensor.fromVector
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]
  congr
  unfold Tensor.toVector
  simp
  apply EqCast.of.SEq
  apply SEq.of.All_EqGetS.Eq (by simp)
  intro i
  simp
  apply Eq.of.EqDataS
  have hi := LtVal i
  have hi : i < n := by
    simp_all
  have h := GetSplitAt_1.eq.GetUnflatten.of.Lt hi (List.Vector.map data v).flatten
  simp at h
  rw [h]
  simp [EqUnflattenFlatten]



-- created on 2025-10-07
