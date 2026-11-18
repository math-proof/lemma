module

public import Batteries.Data.List.Lemmas
public import Def.Data.Nat.Nat
public import Instance.Data.Vector.Vector
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
public import Def.Data.Tensor.Defs.Part2

@[expose] public section

open Bool Nat Int List Lean


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

