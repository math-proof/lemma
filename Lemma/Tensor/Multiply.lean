import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEqMultiply
open Bool Tensor


/--
Commutativity of `Tensor.multiply` when both arguments have the same shape.
-/
@[main]
private lemma Comm
  [CommMagma α]
-- given
  (A : Tensor α s)
  (B : Tensor α s) :
-- imply
  A.multiply B = B.multiply A := by
-- proof
  apply Eq.of.SEq
  apply SEqMultiply


-- created on 2026-09-06
-- updated on 2026-09-07
