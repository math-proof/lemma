import sympy.sets.sets
import Lemma.Set.InAdd.of.In_Ico
import Lemma.Algebra.Sub.eq.Add_Neg
open Set Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Ico a b)
  (d : α) :
-- imply
  x - d ∈ Ico (a - d) (b - d) := by
-- proof
  have := InAdd.of.In_Ico h (-d)
  simp only [Add_Neg.eq.Sub] at this
  assumption


-- created on 2025-08-02
