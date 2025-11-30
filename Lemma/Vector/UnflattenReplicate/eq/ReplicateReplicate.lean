import Lemma.Vector.EqUnflatten.is.Eq_Flatten
import Lemma.Vector.FlattenReplicateReplicate.eq.Replicate
open Vector


@[main]
private lemma main
-- given
  (m n : ℕ)
  (x : α) :
-- imply
  (List.Vector.replicate (m * n) x).unflatten = List.Vector.replicate m (List.Vector.replicate n x) := by
-- proof
  apply EqUnflatten.of.Eq_Flatten
  rw [FlattenReplicateReplicate.eq.Replicate]


-- created on 2025-11-30
