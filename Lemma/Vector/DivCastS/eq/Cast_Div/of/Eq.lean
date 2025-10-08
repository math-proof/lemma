import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main]
private lemma main
  [Div α]
-- given
  (h : n = n')
  (a b : List.Vector α n) :
-- imply
  have h := (congrArg (List.Vector α) h)
  cast h a / cast h b = cast h (a / b) := by
-- proof
  intro h
  ext i
  rw [GetDiv.eq.DivGetS.fin]
  repeat rw [GetCast.eq.Get.of.Eq.fin (by assumption)]
  rw [GetDiv.eq.DivGetS.fin]


-- created on 2025-10-08
