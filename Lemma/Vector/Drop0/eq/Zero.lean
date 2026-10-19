import Lemma.Vector.DropReplicate.eq.Replicate
open Vector


@[path]
private lemma main
  [Zero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n).drop d = 0 := by
-- proof
  repeat rw [Zero.eq.Replicate]
  rw [DropReplicate.eq.Replicate]


-- created on 2025-11-30
