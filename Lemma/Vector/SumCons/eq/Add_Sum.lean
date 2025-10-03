import sympy.vector.vector
import Lemma.Algebra.SumCons.eq.Add_Sum
open Algebra


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (a : α)
  (l : List.Vector α n) :
-- imply
  (a ::ᵥ l).sum = a + l.sum :=
-- proof
  SumCons.eq.Add_Sum


-- created on 2025-10-03
