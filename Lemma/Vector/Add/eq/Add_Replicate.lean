import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetAdd.eq.AddGet
open Vector


@[main]
private lemma main
  [Add α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  x + a = x + List.Vector.replicate n a := by
-- proof
  ext i
  rw [GetAdd.eq.AddGet.fin]
  simp [GetAdd.eq.AddGetS.fin]


-- created on 2025-12-01
