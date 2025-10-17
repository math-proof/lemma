import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Bool.SEq.is.Eq
open Tensor Bool


@[main, comm, mp, mpr]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s') :
-- imply
  A ≃ B ↔ A.data ≃ B.data := by
-- proof
  subst h_s
  repeat rw [SEq.is.Eq]
  apply Tensor.Eq.is.EqDataS


-- created on 2025-06-29
