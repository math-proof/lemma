import sympy.functions.elementary.integers
import Lemma.Algebra.Eq.of.Le.Ge
import Lemma.Algebra.GeAddSub_1
import Lemma.Algebra.GeAddSub_1.of.Lt_0
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n < 0) :
-- imply
  n = n - 1 + 1 := by
-- proof
  have h_ge := GeAddSub_1 n
  have h_le := GeAddSub_1.of.Lt_0 h
  apply Eq.of.Le.Ge h_ge h_le


-- created on 2025-08-13
