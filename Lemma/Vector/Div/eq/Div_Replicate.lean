import sympy.vector.vector
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.EqGetReplicate
open Vector


@[main]
private lemma main
  [Div α]
  {n : ℕ}
-- given
  (v : List.Vector α n)
  (d : α) :
-- imply
  v / d = v / (List.Vector.replicate n d) := by
-- proof
  ext i
  rw [GetDiv.eq.DivGet.fin]
  rw [GetDiv.eq.DivGetS.fin]
  rw [EqGetReplicate]


-- created on 2025-10-11
