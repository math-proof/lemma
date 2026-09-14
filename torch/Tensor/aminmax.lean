import sympy.tensor.tensor
import sympy.vector.functions
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.List.ProdTake_1.eq.Get_0.of.GtLength_0
import Lemma.List.ProdTake.ne.Zero.of.NeProd_0
import Lemma.List.ProdTail.ne.Zero.of.NeProd_0
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail
import Lemma.List.EqEraseIdx.of.LeLength
open List Tensor Nat

/--
Reduces the tensor along `dim` by taking the minimum/maximum value.
[aminmax](https://pytorch.org/docs/stable/generated/torch.Tensor.aminmax.html)
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
        (by simp_all [EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail h_lt 1])
        (Tensor.OfVector (X.toVector.map (·.aminmax cmp dim)))
  else
    cast (by simp at h_dim; rw [EqEraseIdx.of.LeLength h_dim]) X

/--
Reduces the tensor along `dim` by returning the indices of the minimum/maximum values.
Analogous to `Tensor.aminmax` but returns indices.
-/
def Tensor.argAminmax [NeZero s.prod] (X : Tensor α s) (cmp : α → α → Prop) [DecidableRel cmp] (dim : Fin s.length) : Tensor (Fin s[dim]) (s.eraseIdx dim) :=
  match h : dim with
  | ⟨0, h_dim⟩ =>
    have : NeZero (s.take 1).prod := ⟨ProdTake.ne.Zero.of.NeProd_0 (NeZero.ne s.prod) 1⟩
    ⟨cast (by simp_all [ProdTake_1.eq.Get_0.of.GtLength_0 h_dim]) ((X.data.splitAt 1).argAminmax cmp)⟩
  | ⟨dim + 1, h_dim⟩ =>
    have h_lt : dim < s.tail.length := by
      simp
      apply Lt_Sub.of.LtAdd h_dim
    have : NeZero s.tail.prod := ⟨ProdTail.ne.Zero.of.NeProd_0 (NeZero.ne s.prod)⟩
    cast
      (by simp_all [EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail h_lt 1])
      (Tensor.OfVector (X.toVector.map (·.argAminmax cmp ⟨dim, h_lt⟩)))
