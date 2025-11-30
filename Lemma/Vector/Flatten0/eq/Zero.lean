import Lemma.Vector.FlattenReplicateReplicate.eq.Replicate
import Lemma.Vector.Zero.eq.Replicate
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (m n : ℕ) :
-- imply
  (0 : List.Vector (List.Vector α n) m).flatten = 0 := by
-- proof
  repeat rw [Zero.eq.Replicate]
  apply FlattenReplicateReplicate.eq.Replicate


-- created on 2025-11-30
