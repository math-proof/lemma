import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetBroadcastMatmul.as.BroadcastMatmulRecGet.of.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength
open Tensor Bool


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s : List ℕ}
-- given
  (h : s.length > 0)
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α [n, k])
  (i : Fin s[0]) :
-- imply
  let Xi : Tensor α (s.tail ++ [m, n]) := cast (by grind) (X[i]'(GtLength.of.GtLength (by simpa) X ⟨i, by grind⟩ (j := 2)))
  have h_i := GtLength.of.GtLength (by simp [broadcast_shape]; grind) (X.broadcast_matmul Y (s' := [])) ⟨i, by simp [broadcast_shape]; split_ifs; repeat simp_all⟩ (j := 2)
  have h_s : broadcast_shape s.tail s.tail ++ [m, k] = (broadcast_shape s [] ++ [m, k]).tail := by
    simp [broadcast_shape]
    split_ifs
    repeat simp; grind
  (X.broadcast_matmul Y)[i] = cast (congrArg (Tensor α) h_s) (Xi.broadcast_matmul_rec (Y.broadcast (s.tail ++ [n, k]) (by simp)) (by grind)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetBroadcastMatmul.as.BroadcastMatmulRecGet.of.GtLength_0 h


-- created on 2026-01-13
