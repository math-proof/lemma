import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetTranspose.eq.Get
open Vector


@[main, comm]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (f : α → β) :
-- imply
  (v.map (·.map f)).transpose = (v.transpose).map (·.map f) := by
-- proof
  ext i j
  simp [GetTranspose.eq.Get.fin]


-- created on 2026-08-07
