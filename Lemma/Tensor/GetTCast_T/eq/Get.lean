import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.EqTT
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.TCast.as.T.of.Eq
open Bool List Tensor


@[main, fin]
private lemma main
-- given
  (X : Tensor α [m, n])
  (i : Fin m) :
-- imply
  (cast (congrArg (Tensor α) (EqSwap_0'1 m n)) Xᵀ)ᵀ[i] = X[i] := by
-- proof
  apply Eq.of.SEq
  apply SEqGetS.of.SEq.GtLength i.isLt
  apply (TCast.as.T.of.Eq (EqSwap_0'1 m n) Xᵀ).trans
  apply SEq.of.Eq
  apply EqTT


-- created on 2026-08-17
-- updated on 2026-08-19
