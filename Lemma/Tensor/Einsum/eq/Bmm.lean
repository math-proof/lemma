import Lemma.Bool.EqCast.of.SEq
import Lemma.Nat.EqMax
import Lemma.Tensor.SEqResize.of.Eq_Get
import Lemma.Tensor.Tensordot.eq.Bmm
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
  rw [EqMax]
  erw [Resize.eq.Cast.of.Eq_Get (i := ⟨0, by grind⟩) (by grind)]
  erw [Resize.eq.Cast.of.Eq_Get (i := ⟨1, by grind⟩) (by grind)]
  simp
  rw [Tensordot.eq.Bmm]
  rfl


-- created on 2026-07-15
