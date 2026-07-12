import Lemma.Vector.EqReplicate0_0
import Lemma.Vector.Flatten0.eq.Zero
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length):
-- imply
  X.repeat i 0 = 0 := by
-- proof
  sorry

-- created on 2026-07-12
