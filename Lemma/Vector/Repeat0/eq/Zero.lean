import Lemma.Vector.RepeatReplicate.eq.Replicate
import Lemma.Vector.Zero.eq.Replicate
import sympy.vector.Basic
open Vector


@[main]
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
