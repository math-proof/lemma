import Lemma.Vector.EqGetReplicate
import Lemma.Vector.GetTake.eq.Get.of.Lt_Min
open Vector


@[main]
private lemma main
-- given
  (x : α)
  (n d : ℕ) :
-- imply
  (List.Vector.replicate n x).take d = List.Vector.replicate (d ⊓ n) x := by
-- proof
  ext i
  rw [GetTake.eq.Get.of.Lt_Min.fin]
  repeat rw [EqGetReplicate]


-- created on 2025-11-30
