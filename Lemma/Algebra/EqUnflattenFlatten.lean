import Lemma.Algebra.EqFlattenUnflatten
import Lemma.Algebra.Eq.of.EqFlattenS
open Algebra


@[main, comm]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten.unflatten = v := by
-- proof
  apply Eq.of.EqFlattenS
  apply EqFlattenUnflatten


-- created on 2025-05-31
