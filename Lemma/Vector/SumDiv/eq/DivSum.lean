import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.GetDiv.eq.DivGet
import Lemma.Finset.DivSum.eq.Sum_Div
open Vector Finset


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  (x / a).sum = x.sum / a := by
-- proof
  repeat rw [Sum.eq.Sum_Get]
  simp only [GetDiv.eq.DivGet]
  rw [Sum_Div.eq.DivSum]


-- created on 2025-09-22
-- updated on 2025-09-23
