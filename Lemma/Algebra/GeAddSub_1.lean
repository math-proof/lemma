import sympy.functions.elementary.integers
import Lemma.Algebra.NotGe.is.Lt
import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Algebra.Lt_Add_1
import Lemma.Algebra.Lt.of.Le.Lt
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n - 1 + 1 ≥ n := by
-- proof
  by_contra h
  have h := Lt.of.NotGe h
  have h := Le_Sub_1.of.Lt h
  have h' := Lt_Add_1 (n - 1)
  have h := Lt.of.Le.Lt h h'
  simp at h


-- created on 2025-08-13
