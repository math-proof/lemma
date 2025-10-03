import sympy.tensor.tensor
import sympy.vector.functions
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Algebra.EqAdd_Sub.of.Ge
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.EqGetInsertIdx.of.Lt_Length
import Lemma.List.DropInsertIdx.eq.Drop.of.Lt
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
open Tensor Algebra Logic List

/--
[exp](https://pytorch.org/docs/stable/generated/torch.exp.html)
-/
instance [Exp α] : Exp (Tensor α s) where
  exp X := ⟨Exp.exp X.data⟩
  exp_add x y := by
    apply Eq.of.EqDataS
    rw [DataAdd.eq.AddDataS]
    rw [DataMul.eq.MulDataS]
    apply Exp.exp_add

/--
[log](https://pytorch.org/docs/stable/generated/torch.log.html)
-/
instance [Log α] : Log (Tensor α s) where
  log X := ⟨Log.log X.data⟩


/--
Tensor.sum (keepdim=True)
-/
def Tensor.sum_keepdim [Add α] [Zero α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  if h : dim < s.length then
    let x_sum := X.sum dim
    let x_sum := x_sum.unsqueeze dim
    have h_dim : dim ≤ (s.eraseIdx dim).length := by
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h]
      apply Le_Sub_1.of.Lt h
    have h_dim : dim < ((s.eraseIdx dim).insertIdx dim 1).length := by
      rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h_dim]
      rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h]
      rwa [EqAdd_Sub.of.Ge]
      apply Ge_1.of.Gt h
    let x_sum := x_sum.repeat s[dim] ⟨dim, h_dim⟩
    cast
      (by
        rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length (by simp [h_dim])]
        rw [TakeInsertIdx.eq.Take.of.Ge (by simp)]
        rw [TakeEraseIdx.eq.Take.of.Ge (by simp)]
        simp only [GetElem.getElem]
        rw [EqGetInsertIdx.of.Lt_Length.fin (by assumption)]
        rw [DropInsertIdx.eq.Drop.of.Lt (by simp)]
        rw [DropEraseIdx.eq.Drop.of.Le (by rfl)]
        simp
      )
      x_sum
  else
    X

/--
[softmax](https://pytorch.org/docs/stable/generated/torch.softmax.html)
-/
def Tensor.softmax [Zero α] [Div α] [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := exp x
  x_exp / x_exp.sum_keepdim dim
