import Batteries.Data.List.Lemmas
import stdlib.Nat
import sympy.vector.vector
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
open Bool Nat Int List Lean

/--
the concept of a Tensor is a generalization of a matrix, like the Tensor concept in pytorch / tensorflow
the declaration syntax is similar
```lean
-- in lean:
import torch.Tensor
def n : ℕ := 2
def m : ℕ := 2
def l : ℕ := 2
def X : Tensor Float [n, m, l] := ⟨List.Vector.replicate (n * m * l) default⟩
#print X
```
```python
# in pytorch:
from torch import Tensor
n : int = 2
m : int = 2
l : int = 2
X = torch.Tensor(m, n, l).to(dtype=torch.float)
print(X)
```
-/
structure Tensor (α : Type _) (shape : List ℕ) where
  data : List.Vector α shape.prod

@[app_unexpander Tensor.mk]
def Tensor.mk.unexpand : PrettyPrinter.Unexpander
  | `($_ $data) => `(⟨$data⟩)
  | _  =>
    throw ()


def Tensor.length  (X : Tensor α shape)  : ℕ :=
  match shape with
  | [] => 0
  | length :: _ => length

instance [Inhabited α] : Inhabited (Tensor α shape) where
  default := ⟨default⟩

def Tensor.toVector (X : Tensor α s) : List.Vector (Tensor α s.tail) (s.headD 1) :=
  cast (by rw [ProdTake_1.eq.HeadD_1]) ((X.data.splitAt 1).map fun v : List.Vector α (s.drop 1).prod => (⟨cast (by simp) v⟩ : Tensor α s.tail))

instance [Zero α] : Zero (Tensor α s) := ⟨⟨Zero.zero⟩⟩

instance [One α] : One (Tensor α s) := ⟨⟨One.one⟩⟩

instance [AddMonoidWithOne α] [CharZero α] : NatCast (Tensor α []) where
  natCast n := ⟨[n], by simp⟩

instance [NNRatCast α] : NNRatCast (Tensor α s) where
  nnratCast q := ⟨NNRatCast.nnratCast q⟩

instance [Add α] : Add (Tensor α s) where
  add A B := ⟨A.data + B.data⟩

instance [Add α] : HAdd (Tensor α s) α (Tensor α s) where
  hAdd A b := ⟨A.data + b⟩

instance [Add α] : HAdd (Tensor α s) (Tensor α []) (Tensor α s) where
  hAdd A B := A + B.data[0]

instance [Sub α] : HSub (Tensor α s) α (Tensor α s) where
  hSub A b := ⟨A.data - b⟩

instance [Sub α] : HSub (Tensor α s) (Tensor α []) (Tensor α s) where
  hSub A B := A - B.data[0]

instance [Mul α] : Mul (Tensor α s) where
  mul A B := ⟨A.data * B.data⟩

instance [Mul α] : HMul (Tensor α s) (Tensor α []) (Tensor α s) where
  hMul A b := ⟨A.data * b.data[0]⟩

instance [Mul α] : HMul α (Tensor α s) (Tensor α s) where
  hMul a B := ⟨a * B.data⟩

instance [Mul α] : HMul (Tensor α s) α (Tensor α s) where
  hMul A b := ⟨A.data * b⟩

instance [Div α] : Div (Tensor α s) where
  div A B := ⟨A.data / B.data⟩

instance [Div α] : HDiv (Tensor α s) α (Tensor α s) where
  hDiv A b := ⟨A.data / b⟩

instance [Div α] : HDiv (Tensor α s) (Tensor α []) (Tensor α s) where
  hDiv A b := ⟨A.data / b.data[0]⟩

instance [Neg α] : Neg (Tensor α s) where
  neg X := ⟨-X.data⟩

instance [Inv α] : Inv (Tensor α s) where
  inv X := ⟨X.data⁻¹⟩

/-- Append two tensors. -/
instance : HAppend (Tensor α (n :: s)) (Tensor α (m :: s)) (Tensor α ((n + m) :: s)) where
  hAppend A B := ⟨cast (by simp [right_distrib]) (A.data ++ B.data)⟩

/--
Append two tensors with batching.
-/
instance : HAppend (Tensor α (b_z ++ m :: s)) (Tensor α (b_z ++ n :: s)) (Tensor α (b_z ++ (m + n) :: s)) where
  hAppend A B :=
    let a : List.Vector (List.Vector α (m * s.prod)) b_z.prod := cast (by simp) (A.data.splitAt b_z.length)
    let b : List.Vector (List.Vector α (n * s.prod)) b_z.prod := cast (by simp) (B.data.splitAt b_z.length)
    ⟨cast (congrArg (List.Vector α) (by grind)) (List.Vector.map₂ HAppend.hAppend a b).flatten⟩

instance [LE α] : LE (Tensor α s) where
  le A B := A.data ≤ B.data

instance [LT α] : LT (Tensor α s) where
  lt A B := A.data < B.data

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

instance : Coe α (Tensor α []) where
  coe x := ⟨[x], by simp⟩

instance [Coe α β] : Coe (Tensor α s) (Tensor β s) where
  coe X := X.map Coe.coe

def Tensor.broadcast_shape (s : List ℕ) (s' : List ℕ) : List ℕ :=
  let ⟨batch_size, s, s'⟩ : List ℕ × List ℕ × List ℕ :=
    if _ : s.length < s'.length then
      ⟨s'.take (s'.length - s.length), s, (s'.drop (s'.length - s.length))⟩
    else if _ : s.length > s'.length then
      ⟨s.take (s.length - s'.length), (s.drop (s.length - s'.length)), s'⟩
    else
      ⟨[], s, s'⟩
  batch_size ++ List.zipWith (fun a b => a ⊔ b) s s'

def Tensor.matmul_shape (s : List ℕ) (s' : List ℕ) : List ℕ :=
  if h : s.length = 0 then
    s' -- reduced to scalar product
  else if h : s'.length = 0 then
    s -- reduced to scalar product
  else if h : s.length = 1 then
    s'.eraseIdx (s'.length - 2)
  else if h : s'.length = 1 then
    s.eraseIdx (s.length - 1)
  else
    broadcast_shape (s.take (s.length - 2)) (s'.take (s'.length - 2)) ++ [s[s.length - 2], s'[s'.length - 1]]
