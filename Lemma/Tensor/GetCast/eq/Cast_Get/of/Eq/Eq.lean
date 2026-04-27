import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Tensor.GetCast.as.Get.of.Eq.Eq
open Bool Tensor


@[main, fin]
private lemma val
-- given
  (h_s : s = s')
  (h_m : m = m')
  (v : List.Vector (Tensor α s) m)
  (i : Fin m) :
-- imply
  (cast (congrArg₂ (fun s => List.Vector (Tensor α s)) h_s h_m) v)[i] = cast (congrArg (Tensor α) h_s) v[i] := by
-- proof
  apply Eq_Cast.of.SEq.Eq h_s
  apply GetCast.as.Get.of.Eq.Eq.val h_s h_m


@[main, fin]
private lemma main
-- given
  (h_s : s = s')
  (h_m : m = m')
  (v : List.Vector (Tensor α s) m)
  (i : Fin m') :
-- imply
  (cast (congrArg₂ (fun s => List.Vector (Tensor α s)) h_s h_m) v)[i] = cast (congrArg (Tensor α) h_s) v[i] := by
-- proof
  apply Eq_Cast.of.SEq.Eq h_s
  apply GetCast.as.Get.of.Eq.Eq h_s h_m


-- created on 2026-04-27
