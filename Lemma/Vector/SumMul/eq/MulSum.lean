import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Finset.MulSum.eq.Sum_Mul
open Vector Finset


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  (x * a).sum = x.sum * a := by
-- proof
  repeat rw [Sum.eq.Sum_Get]
  simp only [GetMul.eq.MulGet]
  rw [Sum_Mul.eq.MulSum]


-- created on 2025-09-24
