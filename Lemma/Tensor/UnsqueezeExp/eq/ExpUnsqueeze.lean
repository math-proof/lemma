import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.DataUnsqueeze.eq.Cast_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.SEqExpS.of.SEq
open Bool List Tensor Vector


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (exp X).unsqueeze d = exp (X.unsqueeze d) := by
-- proof
  apply Eq.of.EqDataS
  rw [DataExp.eq.ExpData]

  have h_s := ProdInsertIdx.eq.Prod s d
  symm at h_s
  apply EqCast.of.SEq.Eq h_s
  simp [DataUnsqueeze.eq.Cast_Data]
  apply SEqExpS.of.SEq
  apply SEq_Cast.of.Eq h_s


-- created on 2025-12-04
