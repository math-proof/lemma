import Lemma.Set.InAdd.of.In_Icc
import Lemma.Int.Sub.eq.Add_Neg
open Set Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b d : α}
-- given
  (h : x ∈ Icc a b)
  (d : α) :
-- imply
  x - d ∈ Icc (a - d) (b - d) := by
-- proof
  have := InAdd.of.In_Icc h (-d)
  simp only [Add_Neg.eq.Sub] at this
  assumption


-- created on 2026-10-03
