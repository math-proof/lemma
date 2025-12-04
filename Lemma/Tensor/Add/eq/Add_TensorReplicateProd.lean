import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetAdd.eq.AddGetS
open Tensor Vector


@[main]
private lemma main
  [Add α]
-- given
  (X : Tensor α s)
  (δ : α) :
-- imply
  X + δ = X + (⟨List.Vector.replicate s.prod δ⟩ : Tensor α s) := by
-- proof
  conv_lhs => simp [HAdd.hAdd]
  apply Eq.of.EqDataS
  simp [DataAdd.eq.AddDataS]
  ext t
  simp [GetAdd.eq.AddGetS.fin]
  simp [HAdd.hAdd]


-- created on 2025-12-04
