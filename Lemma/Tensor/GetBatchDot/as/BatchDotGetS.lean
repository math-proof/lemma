import Lemma.Bool.SEq.is.SEqCast.of.Eq
import sympy.tensor.tensor
open Bool


@[main, cast]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α ((b :: bz) ++ [m, k]))
  (Y : Tensor α ((b :: bz) ++ [k, n]))
  (i : Fin b) :
-- imply
  (X.batch_dot Y).get i ≃ (X.get i).batch_dot (Y.get i) := by
-- proof
  simp [Tensor.batch_dot]
  apply SEq_Cast.of.SEq.Eq (by grind)
  sorry


-- created on 2026-06-24
-- updated on 2026-06-28
