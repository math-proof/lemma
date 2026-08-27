import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Nat.EqMax
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.Tensordot.eq.Bmm
import Lemma.Tensor.SEqBmmS.of.SEq.SEq
open Bool Nat Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [m, n])
  (Y : Tensor α [n, k]) :
-- imply
  X.einsum Y = X.bmm Y := by
-- proof
  unfold Tensor.einsum
  simp
  apply EqCast.of.SEq
  erw [Resize.eq.Cast.of.Eq_Get (i := ⟨0, by grind⟩) (by grind)]
  erw [Resize.eq.Cast.of.Eq_Get (i := ⟨1, by grind⟩) (by grind)]
  simp
  rw [Tensordot.eq.Bmm]
  apply SEqBmmS.of.SEq.SEq <;>
  ·
    repeat apply SEqCast.of.SEq.Eq (by simp)
    apply SEqCast.of.Eq
    simp [broadcast_shape]


-- created on 2026-07-15
-- updated on 2026-08-27
