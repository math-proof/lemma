import Lemma.Vector.TakeReplicate.eq.Replicate
import Lemma.Vector.Zero.eq.Replicate
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n).take d = 0 := by
-- proof
  repeat rw [Zero.eq.Replicate]
  rw [TakeReplicate.eq.Replicate]


-- created on 2025-11-30
