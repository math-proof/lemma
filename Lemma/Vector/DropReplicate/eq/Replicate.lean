import Lemma.Vector.EqGetReplicate
import Lemma.Vector.GetDrop.eq.Get_Add.of.Lt_Sub
import sympy.vector.vector
open Vector


@[main]
private lemma main
-- given
  (x : α)
  (n d : ℕ) :
-- imply
  (List.Vector.replicate n x).drop d = List.Vector.replicate (n - d) x := by
-- proof
  ext i
  rw [GetDrop.eq.Get_Add.of.Lt_Sub.fin]
  repeat rw [EqGetReplicate]


-- created on 2025-11-30
