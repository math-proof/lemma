import Lemma.Int.MulSub.eq.SubMulS
import Lemma.Vector.GetSub.eq.SubGetS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMul.eq.MulGet
open Vector Int


@[main, comm]
private lemma main
  [NonUnitalNonAssocRing α]
-- given
  (a b : List.Vector α n)
  (x : α) :
-- imply
  (a - b) * x = a * x - b * x := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [GetMul.eq.MulGet]
  repeat rw [GetSub.eq.SubGetS]
  repeat rw [GetMul.eq.MulGet]
  rw [MulSub.eq.SubMulS]


-- created on 2025-12-29
