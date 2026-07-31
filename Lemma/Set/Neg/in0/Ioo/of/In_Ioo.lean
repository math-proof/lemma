import sympy.sets.sets
import Lemma.Int.LtNegS.of.Gt
open Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Ioo a b) :
-- imply
  -x ∈ Ioo (-b) (-a) :=
-- proof
  ⟨LtNegS.of.Gt h.right, LtNegS.of.Gt h.left⟩


-- created on 2025-10-01
