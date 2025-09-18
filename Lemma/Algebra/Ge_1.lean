import Lemma.Algebra.LtVal
open Algebra


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  n ≥ 1 := by
-- proof
  have := LtVal i
  linarith


-- created on 2025-06-07
