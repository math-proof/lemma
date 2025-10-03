import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.Eq.of.EqFlattenS
open Vector


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
