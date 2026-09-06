import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Tensor.MultiplyMultiply.as.Multiply_Multiply
open Bool Tensor


/--
Associativity of `Tensor.multiply` when all three arguments have the same shape.
Both associations then have shape `s`.
-/
@[main]
private lemma main
  [Semigroup α]
-- given
  (A : Tensor α s)
  (B : Tensor α s)
  (C : Tensor α s) :
-- imply
  have hL : multiply_shape (multiply_shape s s) s = s := by
    simp [multiply_shape_self]
  have hR : multiply_shape s (multiply_shape s s) = s := by
    simp [multiply_shape_self]
  cast (congrArg (Tensor α) hL) ((A.multiply B).multiply C) =
    cast (congrArg (Tensor α) hR) (A.multiply (B.multiply C)) := by
-- proof
  apply Eq.of.SEq
  apply SEqCastS.of.SEq.Eq.Eq
  ·
    simp [multiply_shape_self]
  ·
    simp [multiply_shape_self]
  apply MultiplyMultiply.as.Multiply_Multiply


-- created on 2026-09-07
