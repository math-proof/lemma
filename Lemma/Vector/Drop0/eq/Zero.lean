import Lemma.Vector.DropReplicate.eq.Replicate
import Lemma.Vector.EqGet0_0
import Lemma.Vector.Zero.eq.Replicate
import sympy.vector.vector
open Vector


@[main]
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
