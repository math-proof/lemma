import Batteries.Data.List.Lemmas
import Def.Data.Nat.Nat
import Instance.Data.Vector.Vector
import Lemma.Bool.UFn.of.Eq
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.Lt.of.Prod.eq.IteGt.Ne
import Lemma.Nat.Max.of.Prod.eq.IteGt
import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail
import Lemma.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx
import Lemma.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Lemma.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Lemma.List.ProdSwap.eq.Prod
import Lemma.List.Rotate_Mod.eq.Rotate
import Lemma.List.EqPermute
import Lemma.List.EqTake.of.LeLength
import Lemma.List.Drop.eq.Nil.of.LeLength
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.Swap.eq.PermutePermute.of.Lt.GtLength
import Lemma.List.Swap.of.Prod.eq.IteGt
import Lemma.List.EqEraseIdx.of.LeLength
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.ProdPermute.eq.MulProd_ProdAppend
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.List.ProdPermute__Neg.eq.MulProd_ProdDrop
import Lemma.List.ProdTake_1.eq.HeadD_1
import Lemma.List.Rotate.eq.AppendDrop__Take
import Instance.Data.Holor.Defs.Part2
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

