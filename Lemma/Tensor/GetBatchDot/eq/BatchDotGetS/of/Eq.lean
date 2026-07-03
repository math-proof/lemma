import Lemma.Tensor.GetBatchDot.eq.BatchDotGetS
open Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : bz = b₀ :: b)
  (X : Tensor α (bz ++ [m, k]))
  (Y : Tensor α (bz ++ [k, n]))
  (i : Fin b₀) :
-- imply
  have h_X : bz ++ [m, k] = (b₀ :: b) ++ [m, k] := by
    rw [h]
  have h_Y : bz ++ [k, n] = (b₀ :: b) ++ [k, n] := by
    rw [h]
  let X := cast (congrArg (Tensor α) h_X) X
  let Y := cast (congrArg (Tensor α) h_Y) Y
  (X.batch_dot Y)[i] = X[i].batch_dot Y[i] := by
-- proof
  intros
  rw [GetBatchDot.eq.BatchDotGetS]


-- created on 2026-07-03
