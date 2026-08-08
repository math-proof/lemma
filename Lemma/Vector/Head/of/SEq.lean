import stdlib.SEq
import Lemma.Vector.Get.of.SEq.Lt
import Lemma.Vector.Head.eq.Get_0
open Vector


@[main]
private lemma main
  {a : List.Vector α (.succ n)}
  {b : List.Vector α (.succ n')}
-- given
  (h : a ≃ b) :
-- imply
  a.head = b.head := by
-- proof
  simp [Head.eq.Get_0]
  exact Get.of.SEq.Lt.fin (by simp) h


-- created on 2026-08-08
