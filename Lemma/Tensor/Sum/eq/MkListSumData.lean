import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.Head.eq.Get_0
open Tensor Vector


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α [n]) :
-- imply
  X.sum = ⟨[X.data.sum], by simp⟩ := by
-- proof
  let ⟨X⟩ := X
  apply Eq.of.EqDataS
  erw [DataSum_0.eq.SumSplitAtData]
  simp
  ext i
  fin_cases i
  have := GetSum.eq.SumMapGet.fin (X.splitAt 1) ⟨0, by simp⟩
  simp at this
  conv_lhs => simp [this]
  apply congrArg
  ext i
  erw [GetMap.eq.UFnGet]
  erw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp


-- created on 2025-10-11
-- updated on 2026-07-22
