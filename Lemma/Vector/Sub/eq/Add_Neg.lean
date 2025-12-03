import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Vector.GetAdd.eq.AddGet
import Lemma.Vector.GetSub.eq.SubGet
open Vector Int


@[main, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  x - a = x + -a := by
-- proof
  ext i
  rw [GetAdd.eq.AddGet.fin]
  rw [GetSub.eq.SubGet.fin]
  rw [Sub.eq.Add_Neg]


-- created on 2025-12-03
