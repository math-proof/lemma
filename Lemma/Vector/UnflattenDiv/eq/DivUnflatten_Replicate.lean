import sympy.vector.vector
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Vector.GetDiv.eq.DivGetS
import Lemma.Vector.EqGetReplicate
open Vector


@[main]
private lemma main
  [Div α]
  {m n : ℕ}
-- given
  (v : List.Vector α (m * n))
  (d : α) :
-- imply
  (v / d).unflatten = v.unflatten / (List.Vector.replicate n d) := by
-- proof
  ext i j
  rw [GetUnflatten.eq.Get_AddMul.fin]
  repeat rw [GetDiv.eq.DivGet.fin]
  rw [GetDiv.eq.DivGetS.fin]
  rw [EqGetReplicate]
  rw [GetUnflatten.eq.Get_AddMul.fin]


-- created on 2025-09-22
-- updated on 2025-09-24
