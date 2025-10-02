import sympy.vector.vector
import Lemma.Algebra.GetVal.eq.Get.of.Lt
import Lemma.Algebra.EqGetRange
open Algebra


@[main]
private lemma main
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n).val[i] = i := by
-- proof
  simp_all [GetVal.eq.Get.of.Lt]
  apply EqGetRange


-- created on 2025-07-05
