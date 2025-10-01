import sympy.sets.sets
import Lemma.Algebra.LeNegS.of.Ge
open Algebra


@[main]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  -x ∈ Icc (-b) (-a) :=
-- proof
  ⟨LeNegS.of.Ge h.right, LeNegS.of.Ge h.left⟩


-- created on 2025-04-04
-- updated on 2025-10-01
