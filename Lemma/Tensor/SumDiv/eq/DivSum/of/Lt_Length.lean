import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataDiv.eq.DivData
import Lemma.Vector.CastSum.eq.DivCastSumSplitAt_1
import Lemma.Tensor.ToVectorDiv.eq.DivToVector_Broadcast
import Lemma.Vector.MapMap.eq.Map_Comp
import Lemma.Algebra.Div.eq.HDiv
import Lemma.Tensor.Div.eq.Div_Broadcast
open Tensor Vector Algebra


@[main]
private lemma main
  [DivisionSemiring α]
-- given
  (h : dim < s.length)
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (X / n).sum dim = X.sum dim / n := by
-- proof
  induction dim generalizing X s with
  | zero =>
    unfold Tensor.sum
    simp [h]
    apply Eq.of.EqDataS
    let ⟨data⟩ := X
    repeat rw [DataDiv.eq.DivData]
    simp_all [CastSum.eq.DivCastSumSplitAt_1]
  | succ dim ih =>
    unfold Tensor.sum
    simp [h]
    match s with
    | .nil =>
      contradiction
    | s₀ :: s =>
      rw [ToVectorDiv.eq.DivToVector_Broadcast]
      simp [MapMap.eq.Map_Comp, HDiv.hDiv]
      apply Eq.of.EqDataS
      simp [Div.eq.HDiv]
      simp [Div_Broadcast.eq.Div]
      simp at h
      simp [ih h]
      sorry


-- created on 2025-09-25
