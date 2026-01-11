import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.GetCast.as.Get.of.Eq
open Tensor Bool


@[main, fin]
private lemma main
-- given
  (h : s = s')
  (v : List.Vector (Tensor α s) n)
  (i : Fin n) :
-- imply
  (cast (congrArg (fun s => List.Vector (Tensor α s) n) h) v)[i] = cast (by simp_all) v[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetCast.as.Get.of.Eq h


-- created on 2026-01-11
