import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Vector.GetCast.as.Get.of.Eq.Eq
open Bool Vector


@[main, fin]
private lemma val
-- given
  (h_n : n = n')
  (h_m : m = m')
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  (cast (congrArg₂ (fun n => List.Vector (List.Vector α n)) h_n h_m) v)[i] = cast (congrArg (List.Vector α) h_n) v[i] := by
-- proof
  apply Eq_Cast.of.SEq.Eq h_n
  apply GetCast.as.Get.of.Eq.Eq.val h_n h_m


@[main, fin]
private lemma main
-- given
  (h_n : n = n')
  (h_m : m = m')
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m') :
-- imply
  (cast (congrArg₂ (fun n => List.Vector (List.Vector α n)) h_n h_m) v)[i] = cast (congrArg (List.Vector α) h_n) v[i] := by
-- proof
  apply Eq_Cast.of.SEq.Eq h_n
  apply GetCast.as.Get.of.Eq.Eq h_n h_m


-- created on 2026-04-27
