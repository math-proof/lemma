import Lemma.Vector.EqReplicate0_0
import Lemma.Vector.Flatten0.eq.Zero
import sympy.vector.Basic
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (v : List.Vector α n) :
-- imply
  v.repeat 0 = (0 : List.Vector α (0 * n)) := by
-- proof
  unfold List.Vector.repeat
  rw [Vector.EqReplicate0_0 v, Flatten0.eq.Zero 0 n]


-- created on 2026-07-12
