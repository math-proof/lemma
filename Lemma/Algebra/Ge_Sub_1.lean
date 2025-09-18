import Lemma.Algebra.LeSub_1
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n ≥ n - 1 :=
-- proof
  LeSub_1 n


-- created on 2025-06-21
