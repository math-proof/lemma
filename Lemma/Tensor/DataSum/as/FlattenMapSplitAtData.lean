import Lemma.Bool.SEq.is.SEqCast.of.Eq
import sympy.tensor.tensor
open Bool


@[main, comm, cast]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α s)
  (i : ℕ) :
-- imply
  (X.sum i).data ≃ ((X.data.splitAt i).map fun x => (x.splitAt 1).sum).flatten := by
-- proof
  unfold Tensor.sum
  simp
  apply SEqCast.of.SEq.Eq (by simp; grind)
  rfl


-- created on 2026-07-22
