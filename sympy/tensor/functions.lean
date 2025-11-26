import sympy.tensor.tensor
import sympy.vector.functions
import Lemma.Nat.Ge.of.NotLt
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.GeLength
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.List.TakeInsertIdx.eq.Take.of.Ge
import Lemma.List.TakeEraseIdx.eq.Take.of.Ge
import Lemma.List.EqGetInsertIdx.of.GeLength
import Lemma.List.DropInsertIdx.eq.Drop.of.Lt
import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.LengthInsertIdxEraseIdx.eq.Length.of.GtLength
import Lemma.List.EqSetInsertIdxEraseIdx.of.GtLength
import Lemma.List.Lt_LengthInsertIdxEraseIdx.of.GtLength
open Algebra List Tensor Nat

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
  exp_zero := by
    apply Eq.of.EqDataS
    apply Exp.exp_zero
  exp_neg x := by
    apply Eq.of.EqDataS
    rw [DataNeg.eq.NegData]
    rw [DataInv.eq.InvData]
    apply Exp.exp_neg

instance [NeZero s.prod] [ExpNeZero α] : ExpNeZero (Tensor α s) where
  exp_ne_zero x := by
    intro h_eq
    rw [Eq.is.EqDataS] at h_eq
    simp [EqData0'0] at h_eq
    have h := ExpNeZero.exp_ne_zero x.data
    contradiction

/--
[log](https://pytorch.org/docs/stable/generated/torch.log.html)
-/
instance [Log α] : Log (Tensor α s) where
  log X := ⟨Log.log X.data⟩


/--
Tensor.sum (keepdim=True)
-/
def Tensor.keepdim (X : Tensor α (s.eraseIdx dim)) : Tensor α s :=
  if h : dim < s.length then
    cast
      (by simp [List.EqSetInsertIdxEraseIdx.of.GtLength h])
      ((X.unsqueeze dim).repeat s[dim] ⟨dim, Lt_LengthInsertIdxEraseIdx.of.GtLength h 1⟩)
  else
    cast (by rw [EqEraseIdx.of.LeLength (Ge.of.NotLt h)]) X

/--
[softmax](https://pytorch.org/docs/stable/generated/torch.softmax.html)
-/
def Tensor.softmax [Exp α] (x : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α s :=
  let x_exp := exp x
  x_exp / (x_exp.sum dim).keepdim
