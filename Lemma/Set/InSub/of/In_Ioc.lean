import Lemma.Set.InAdd.of.In_Ioc
import Lemma.Algebra.Sub.eq.Add_Neg
open Set Algebra


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {x a b : α}
-- given
  (h : x ∈ Ioc a b)
  (d : α) :
-- imply
  x - d ∈ Ioc (a - d) (b - d) := by
-- proof
  have := InAdd.of.In_Ioc h (-d)
  simp only [Add_Neg.eq.Sub] at this
  assumption


-- created on 2025-03-02
-- updated on 2025-08-02
