import sympy.tensor.tensor
import sympy.vector.functions
import Lemma.Nat.Ge.of.NotLt
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
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
import Lemma.List.ProdTake.ne.Zero.of.NeProd_0
import Lemma.List.ProdTail.ne.Zero.of.NeProd_0
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
  log_zero := by
    apply Eq.of.EqDataS
    apply Log.log_zero
  log_one := by
    apply Eq.of.EqDataS
    apply Log.log_one
  log_div_self x := by
    apply Eq.of.EqDataS
    rw [DataDiv.eq.DivDataS]
    rw [EqData0'0]
    apply Log.log_div_self

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


/--
Reduces the tensor along `dim` by taking the minimum/maximum value.
[aminmax](https://pytorch.org/docs/stable/generated/torch.aminmax.html)
-/
def Tensor.aminmax [NeZero s.prod] (X : Tensor α s) (cmp : α → α → Prop) [DecidableRel cmp] (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  if h_dim : dim < s.length then
    match h : dim with
    | 0 =>
      have : NeZero (s.take 1).prod := ⟨ProdTake.ne.Zero.of.NeProd_0 (NeZero.ne s.prod) 1⟩
      ⟨cast (by simp) ((X.data.splitAt 1).aminmax cmp)⟩
    | dim + 1 =>
      have h_lt : dim < s.tail.length := by
        simp
        apply Lt_Sub.of.LtAdd h_dim
      have : NeZero s.tail.prod := ⟨ProdTail.ne.Zero.of.NeProd_0 (NeZero.ne s.prod)⟩
      cast
        (by simp_all [EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail h_lt 1])
        (Tensor.fromVector (X.toVector.map (·.aminmax cmp dim)))
  else
    cast (by simp at h_dim; rw [EqEraseIdx.of.LeLength h_dim]) X

/--
Reduces the tensor along `dim` by taking the minimum value.
[min](https://pytorch.org/docs/stable/generated/torch.min.html)
-/
def Tensor.min [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  X.aminmax GT.gt dim

/--
Reduces the tensor along `dim` by taking the minimum value.
[max](https://pytorch.org/docs/stable/generated/torch.max.html)
-/
def Tensor.max [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : ℕ := s.length - 1) : Tensor α (s.eraseIdx dim) :=
  X.aminmax LT.lt dim


/--
Reduces the tensor along `dim` by returning the indices of the minimum/maximum values.
Analogous to `Tensor.aminmax` but returns indices.
-/
def Tensor.argAminmax [NeZero s.prod] (X : Tensor α s) (cmp : α → α → Prop) [DecidableRel cmp] (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  match h : dim.val with
  | 0 =>
    have : NeZero (s.take 1).prod := ⟨ProdTake.ne.Zero.of.NeProd_0 (NeZero.ne s.prod) 1⟩
    ⟨cast (by simp_all [ProdTake_1.eq.Get_0.of.GtLength_0 (Gt_0 dim)]) ((X.data.splitAt 1).argAminmax cmp)⟩
  | dim + 1 =>
    have h_lt : dim < s.tail.length := by
      simp
      apply Lt_Sub.of.LtAdd
      grind
    have : NeZero s.tail.prod := ⟨ProdTail.ne.Zero.of.NeProd_0 (NeZero.ne s.prod)⟩
    cast
      (by simp_all [EraseIdx.eq.Cons_EraseIdxTail.of.Lt_LengthTail h_lt 1])
      (Tensor.fromVector (X.toVector.map (·.argAminmax cmp ⟨dim, h_lt⟩)))

/--
Returns the indices of the minimum value of a tensor along `dim`.
[argmin](https://pytorch.org/docs/stable/generated/torch.argmin.html)
-/
def Tensor.argmin [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  X.argAminmax GT.gt dim

/--
Returns the indices of the maximum value of a tensor along `dim`.
[argmax](https://pytorch.org/docs/stable/generated/torch.argmax.html)
-/
def Tensor.argmax [NeZero s.prod] [LT α] [DecidableLT α] (X : Tensor α s) (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  X.argAminmax LT.lt dim
