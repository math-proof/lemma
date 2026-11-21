import Lemma.Vector.RepeatReplicate.eq.Replicate
import Theorem.Vector.Zero.eq.Replicate
open Vector


@[path]
private lemma main
  [Zero α]
-- given
  (m n : ℕ) :
-- imply
  (0 : List.Vector α n).repeat m = 0 := by
-- proof
  repeat rw [Zero.eq.Replicate]
  apply RepeatReplicate.eq.Replicate


-- created on 2025-11-30
-- updated on 2026-11-20
