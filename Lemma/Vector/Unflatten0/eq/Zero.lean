import Lemma.Vector.UnflattenReplicate.eq.ReplicateReplicate
import Theorem.Vector.Zero.eq.Replicate
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Unflatten0.eq.Zero |
| comm | Vector.Zero.eq.Unflatten0 |
-/
@[path, comm]
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
-- updated on 2026-11-20
