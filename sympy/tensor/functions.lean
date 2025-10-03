import sympy.tensor.tensor
import sympy.vector.functions
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.Algebra.EqAdd_Sub.of.Ge
import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.Set.eq.AppendTake__Cons_Drop.of.Lt_Length
import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
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
[softmax](https://pytorch.org/docs/stable/generated/torch.softmax.html)
-/
def Tensor.softmax [Zero α] [Div α] [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := exp x
  let x_sum : Tensor α s :=
    if h : dim < s.length then
      let x_sum := x_exp.sum dim
      let x_sum := x_sum.unsqueeze dim
      have h_dim : dim < ((s.eraseIdx dim).insertIdx dim 1).length := by
        rw [LengthInsertIdx.eq.Add1Length.of.Le_Length] <;>
          rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length h]
        .
          rwa [EqAdd_Sub.of.Ge]
          apply Ge_1.of.Gt h
        .
          apply Le_Sub_1.of.Lt h
      let x_sum := x_sum.repeat s[dim] ⟨dim, h_dim⟩
      cast
        (by
          apply EqUFnS.of.Eq
          rw [Set.eq.AppendTake__Cons_Drop.of.Lt_Length (by simp [h_dim])]
          rw [TakeInsertIdx.eq.Take.of.Ge (by simp)]
          rw [TakeEraseIdx.eq.Take.of.Ge (by simp)]
          sorry
        )
        x_sum
    else
      x_exp
  x_exp / x_sum
