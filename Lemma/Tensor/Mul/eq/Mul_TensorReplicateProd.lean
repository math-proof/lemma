import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetMul.eq.MulGetS
open Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (δ : α) :
-- imply
  X * δ = X * (⟨List.Vector.replicate s.prod δ⟩ : Tensor α s) := by
-- proof
  conv_lhs => simp [HMul.hMul]
  apply Eq.of.EqDataS
  simp [DataMul.eq.MulDataS]
  ext t
  simp [GetMul.eq.MulGetS.fin]
  simp [HMul.hMul]


-- created on 2025-12-04
