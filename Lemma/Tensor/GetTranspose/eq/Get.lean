import sympy.tensor.tensor
import Lemma.Vector.EqGetRange.of.Lt
import Lemma.Tensor.Permute__0.eq.Cast
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Vector.Eq.of.Eq_Cast.Eq
import Lemma.Tensor.EqGetS.of.Data.as.FlattenTransposeSplitAt_1
open Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor α [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  Xᵀ[j, i] = X[i, j] := by
-- proof
  unfold Tensor.T
  simp
  unfold Tensor.transpose
  simp [Permute__0.eq.Cast]
  simp [Permute.eq.Ite X]
  unfold Tensor.permuteTail
  split_ifs with h
  ·
    simp
    unfold Tensor.rotate
    split_ifs with h
    ·
      simp at h
    ·
      simp
      have h_cast : List.Vector α (([m, n].drop (1 % [m, n].length)).prod * ([m, n].take (1 % [m, n].length)).prod) = List.Vector α ([m, n].drop (1 % [m, n].length) ++ [m, n].take (1 % [m, n].length)).prod := by
        simp
      let data := cast h_cast (X.data.splitAt 1).transpose.flatten
      have h_data : data = cast h_cast (X.data.splitAt 1).transpose.flatten := rfl
      simp [← h_data]
      let X' : Tensor α [n, m] := ⟨data⟩
      have h_X' : X' = ⟨data⟩ := rfl
      simp [← h_X']
      apply EqGetS.of.Data.as.FlattenTransposeSplitAt_1
      simp [X']
      apply Eq.of.Eq_Cast.Eq
      .
        assumption
      .
        simp
  ·
    simp at h


@[main]
private lemma fin
-- given
  (X : Tensor α [m, n])
  (i : Fin m)
  (j : Fin n) :
-- imply
  (Xᵀ.get j).get i = (X.get i).get j := by
-- proof
  apply main


-- created on 2025-07-13
-- updated on 2025-07-18
