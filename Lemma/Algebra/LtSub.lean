import Lemma.Algebra.LtSub.of.Lt
import Lemma.Algebra.LtVal
open Algebra


@[main]
private lemma main
-- given
  (j : Fin n)
  (i : ℕ) :
-- imply
  j - i < n := by
-- proof
  apply LtSub.of.Lt
  apply LtVal j


-- created on 2025-06-21
