import Lemma.Vector.UnflattenReplicate.eq.ReplicateReplicate
import Lemma.Vector.Zero.eq.Replicate
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (m n : ℕ) :
-- imply
  (0 : List.Vector α (m * n)).unflatten = 0 := by
-- proof
  repeat rw [Zero.eq.Replicate]
  apply UnflattenReplicate.eq.ReplicateReplicate


-- created on 2025-11-30
