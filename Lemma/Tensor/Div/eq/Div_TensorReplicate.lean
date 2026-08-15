import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.Div.eq.Div_Replicate
open Tensor Vector


@[main, comm]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  X / a = X / ⟨List.Vector.replicate s.prod a⟩ := by
-- proof
  apply Eq.of.EqDataS
  change X.data / a = (X / ⟨List.Vector.replicate s.prod a⟩).data
  rw [DataDiv.eq.DivDataS]
  simp
  apply Div.eq.Div_Replicate


-- created on 2026-08-15
