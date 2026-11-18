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
public import Def.Data.Tensor.Defs.Part3

@[expose] public section

open Bool Nat Int List Lean


instance : Coe α (Tensor α []) where
  coe x := ⟨[x], by simp⟩

instance [Coe α β] : Coe (Tensor α s) (Tensor β s) where
  coe X := X.map Coe.coe

