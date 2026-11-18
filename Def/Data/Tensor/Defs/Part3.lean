module

public import Batteries.Data.List.Lemmas
public import Def.Data.Nat.Nat
public import Structure.Data.Tensor.Defs
public import Def.Data.Vector.Basic
public import Theorem.Bool.UFn.of.Eq
public import Theorem.Nat.MulMul.eq.Mul_Mul
public import Theorem.Nat.Lt_Sub.of.LtAdd
public import Theorem.Nat.LtMod.of.Gt_0
public import Theorem.Nat.Gt_0.of.Ne_0
public import Theorem.Nat.Lt.of.Prod.eq.IteGt.Ne
public import Theorem.Nat.Max.of.Prod.eq.IteGt
public import Theorem.Nat.EqMulDiv.of.Dvd
public import Theorem.Int.NegSucc.eq.NegAdd_1
public import Theorem.List.ProdInsertIdx.eq.Prod
public import Theorem.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
public import Theorem.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail
public import Theorem.List.Prod.eq.Mul_ProdTail.of.GtLength_0
public import Theorem.List.EraseIdxAppend.eq.Append_EraseIdx
public import Theorem.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
public import Theorem.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
public import Theorem.List.ProdSwap.eq.Prod
public import Theorem.List.Rotate_Mod.eq.Rotate
public import Theorem.List.EqPermute
public import Theorem.List.EqTake.of.LeLength
public import Theorem.List.Drop.eq.Nil.of.LeLength
public import Theorem.List.LengthDrop.eq.SubLength
public import Theorem.List.Swap.eq.PermutePermute.of.Lt.GtLength
public import Theorem.List.Swap.of.Prod.eq.IteGt
public import Theorem.List.EqEraseIdx.of.LeLength
public import Theorem.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
public import Theorem.List.ProdPermute.eq.MulProd_ProdAppend
public import Theorem.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
public import Theorem.List.ProdPermute__Neg.eq.MulProd_ProdDrop
public import Theorem.List.ProdTake_1.eq.HeadD_1
public import Theorem.List.Rotate.eq.AppendDrop__Take

@[expose] public section
open Bool Nat Int List Lean


def Tensor.OfVector (X : List.Vector (Tensor α s) n) : Tensor α (n :: s) :=
  ⟨(X.map Tensor.data).flatten⟩

/--
index the tensor physically, i.e. calculate the (row-major (C-style)) index in the data vector
given:
  - `indices` - the indices of the tensor
  - `shape` - the shape of the tensor
assuming that indices and shape have the same length
-/
def Tensor.physicalIndex (indices : List ℕ) (shape : List ℕ) : ℕ :=
  let (res, _) := List.foldr
    (fun (i, d) (acc, mult) => (acc + i * mult, mult * d))
    (0, 1)
    (indices.zip shape)
  res

/--
calculate the logical indices of a tensor given the physical index
given:
  - `index` - the physical index of the tensor
  - `shape` - the shape of the tensor
-/
def Tensor.logicalIndices (index : ℕ) (shape : List ℕ) : List ℕ :=
  -- if shape.any (· == 0) then List.replicate shape.length 0 else
  let (res, _) := List.foldr
    (fun d (acc, rem) => (rem % d :: acc, rem / d))
    ([], index)
    shape
  res

def Tensor.map (f : α → β) (X : Tensor α s) : Tensor β s :=
  ⟨X.data.map f⟩

-- Helper: Element-wise zip with function
def Tensor.map₂ (f : α → β → γ) (X : Tensor α s) (Y : Tensor β s) : Tensor γ s :=
  ⟨X.data.map₂ f Y.data⟩

