import sympy.sets.sets
import Lemma.Set.In_Icc.is.InSub
import Lemma.Int.EqSubAdd
open Set Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∉ Icc a b)
  (t : α) :
-- imply
  x + t ∉ Icc (a + t) (b + t) := by
-- proof
  by_contra h
  have := InSub.of.In_Icc t h
  simp only [EqSubAdd] at this
  contradiction


-- created on 2025-05-12
