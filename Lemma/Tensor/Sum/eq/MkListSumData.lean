import sympy.tensor.functions
import Lemma.Nat.Eq_0
import Lemma.Vector.GetSum.eq.SumMapGet
import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.GetSplitAt.eq.Get_AddMul_ProdDrop
open Nat Vector


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (X : Tensor α [n]) :
-- imply
  X.sum = ⟨[X.data.sum], by simp⟩ := by
-- proof
  let ⟨X⟩ := X
  unfold Tensor.sum
  simp
  ext i
  have h_0 := Eq_0 i
  subst h_0
  have := GetSum.eq.SumMapGet.fin (X.splitAt 1) ⟨0, by simp⟩
  simp at this
  conv_lhs =>
    simp [this]
  simp [List.Vector.get]
  apply congrArg
  ext i
  simp
  rw [Head.eq.Get_0.fin]
  rw [GetSplitAt.eq.Get_AddMul_ProdDrop.fin]
  simp


-- created on 2025-10-11
