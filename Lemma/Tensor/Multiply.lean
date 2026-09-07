import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEqMulS
open Bool Tensor


/--
Commutativity of `Tensor.mul` when both arguments have the same shape.
-/
@[main]
private lemma Comm
  [CommMagma α]
-- given
  (A : Tensor α s)
  (B : Tensor α s) :
-- imply
  A.mul B = B.mul A := by
-- proof
  apply Eq.of.SEq
  apply SEqMulS


-- created on 2026-09-06
-- updated on 2026-09-07
