import sympy.sets.sets
import Lemma.Algebra.LeNegS.of.Ge
import Lemma.Int.LtNegS.of.Gt
open Algebra Int


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Ico a b) :
-- imply
  -x ∈ Ioc (-b) (-a) :=
-- proof
  ⟨LtNegS.of.Gt h.right, LeNegS.of.Ge h.left⟩


-- created on 2025-10-01
