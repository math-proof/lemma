import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.Head.eq.Get_0
open Vector


@[main]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod) :
-- imply
  (v.splitAt 0).head = v := by
-- proof
  erw [Head.eq.Get_0.fin]
  apply Eq.of.All_EqGetS.fin
  intros
  erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  aesop


-- created on 2026-05-03
-- updated on 2026-08-24
