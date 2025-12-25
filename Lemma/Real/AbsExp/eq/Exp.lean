import Lemma.Int.EqAbs.of.Gt_0
import Lemma.Real.GtExp_0
import sympy.functions.elementary.exponential
open Int Real


@[main, comm]
private lemma main
  [ExpPos α]
  [IsOrderedAddMonoid α]
-- given
  (x : α) :
-- imply
  |exp x| = exp x :=
-- proof
  EqAbs.of.Gt_0 (GtExp_0 x)


-- created on 2025-12-25
