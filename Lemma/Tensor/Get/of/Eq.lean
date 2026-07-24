import Lemma.Tensor.Get.of.Eq.Lt
open Tensor


@[main, fin]
private lemma main
  {X Y : Tensor α (n :: s)}
-- given
  (h : X = Y) 
  (i : Fin n):
-- imply
  X[i] = Y[i] := by
-- proof
  apply Get.of.Eq.Lt
  aesop


-- created on 2026-01-04
