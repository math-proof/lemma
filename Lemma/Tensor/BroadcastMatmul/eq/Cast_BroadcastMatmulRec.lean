import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.BroadcastMatmul.as.BroadcastMatmulRec
open Tensor Bool


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
  {s : List ℕ}
-- given
  (X : Tensor α (s ++ [m, n]))
  (Y : Tensor α [n, k]) :
-- imply
  have h_s : broadcast_shape s s ++ [m, k] = broadcast_shape s [] ++ [m, k] := by
    simp [broadcast_shape]
    split_ifs
    repeat simp_all
  X.broadcast_matmul Y = cast (congrArg (Tensor α) h_s) (X.broadcast_matmul_rec (Y.broadcast (s ++ [n, k]) (by simp)) (by grind)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply BroadcastMatmul.as.BroadcastMatmulRec


-- created on 2026-01-13
