import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.TransposeUnsqueeze_Length.as.Unsqueeze
open Bool Tensor Fin List Nat Vector


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n]) :
-- imply
  (X.unsqueeze 1)ᵀ = X.unsqueeze 0 := by
-- proof
  have := TransposeUnsqueeze_Length.as.Unsqueeze X
  simp at this
  apply Eq.of.SEq this


@[main]
private lemma deux
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [m, n]) :
-- imply
  (X.unsqueeze 2)ᵀ = X.unsqueeze 1 := by
-- proof
  have := TransposeUnsqueeze_Length.as.Unsqueeze X
  simp at this
  apply Eq.of.SEq this


-- created on 2026-07-11
