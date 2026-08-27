import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.DotT.eq.Dot
import Lemma.Tensor.EqTT
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.TCast.as.T.of.Eq
open Bool Tensor


@[main]
private lemma main
  [CommMagma α] [AddCommMonoid α]
-- given
  (A : Tensor α [n])
  (X : Tensor α [m, n]) :
-- imply
  A @ Xᵀ ≃ X @ A := by
-- proof
  have hshape : [m, n].swap ([m, n].length - 2) ([m, n].length - 1) = [n, m] := by
    simp
  let XT : Tensor α [n, m] := cast (congrArg (Tensor α) hshape) Xᵀ
  apply (SEqDotS.of.SEq.left (SEqCast.of.Eq hshape Xᵀ) A).trans
  have h := DotT.eq.Dot XT A
  apply (SEq.of.Eq h.symm).trans
  apply SEqDotS.of.SEq
  apply (TCast.as.T.of.Eq hshape Xᵀ).trans
  apply SEq.of.Eq
  apply EqTT


-- created on 2026-08-17
-- updated on 2026-08-18
