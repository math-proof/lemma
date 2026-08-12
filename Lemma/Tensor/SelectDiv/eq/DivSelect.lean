import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.SelectDiv.eq.DivSelectS
import Lemma.Tensor.SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx
import Lemma.Vector.Div.eq.Div_Replicate
open Tensor Vector


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (X / B).select d i = X.select d i / B := by
-- proof
  let R : Tensor α s := ⟨List.Vector.replicate s.prod B.data[0]⟩
  have hX : X / B = X / R := by
    apply Eq.of.EqDataS
    simp only [HDiv.hDiv, R]
    apply Div.eq.Div_Replicate
  rw [hX]
  simp only [R]
  rw [SelectDiv.eq.DivSelectS]
  rw [SelectTensorReplicateProd.eq.TensorReplicateProdEraseIdx]
  apply Eq.of.EqDataS
  simp only [HDiv.hDiv]
  symm
  apply Div.eq.Div_Replicate


-- created on 2026-08-12
