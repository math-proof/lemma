import sympy.sets.sets
import Lemma.Int.LeNegS.of.Ge
import Lemma.Int.LtNegS.of.Gt
open Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Ioc a b) :
-- imply
  -x ∈ Ico (-b) (-a) :=
-- proof
  ⟨LeNegS.of.Ge h.right, LtNegS.of.Gt h.left⟩


-- created on 2025-10-01
