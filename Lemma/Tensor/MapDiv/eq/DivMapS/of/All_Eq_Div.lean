import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.MapDiv.eq.DivMap.of.All_Eq_Div
import Lemma.Vector.MapDiv.eq.DivMapS.of.All_Eq_Div
import Lemma.Vector.GetMap.eq.UFnGet
open Tensor Vector


@[main, comm]
private lemma main
  [Div α]
  [Div β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a / b) = f a / f b)
  (A B : Tensor α s) :
-- imply
  (A / B).map f = A.map f / B.map f := by
-- proof
  apply Eq.of.EqDataS
  simp [Tensor.map]
  rw [DataDiv.eq.DivDataS]
  apply MapDiv.eq.DivMapS.of.All_Eq_Div hf


@[main, comm]
private lemma scalar
  [Div α]
  [Div β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a / b) = f a / f b)
  (A : Tensor α s)
  (b : Tensor α []) :
-- imply
  (A / b).map f = A.map f / b.map f := by
-- proof
  apply Eq.of.EqDataS
  unfold Tensor.map
  simp [DataDiv.eq.DivData]
  rw [MapDiv.eq.DivMap.of.All_Eq_Div hf]
  simp only [GetElem.getElem]
  erw [GetMap.eq.UFnGet.fin]


-- created on 2026-08-08
