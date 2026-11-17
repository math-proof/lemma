import Batteries.Data.List.Lemmas
import Def.Data.Nat.Nat
import Instance.Data.Vector.Vector
import Theorem.Bool.UFn.of.Eq
import Theorem.Nat.MulMul.eq.Mul_Mul
import Theorem.Nat.Lt_Sub.of.LtAdd
import Theorem.Nat.LtMod.of.Gt_0
import Theorem.Nat.Gt_0.of.Ne_0
import Theorem.Nat.Lt.of.Prod.eq.IteGt.Ne
import Theorem.Nat.Max.of.Prod.eq.IteGt
import Theorem.Nat.EqMulDiv.of.Dvd
import Theorem.Int.NegSucc.eq.NegAdd_1
import Theorem.List.ProdInsertIdx.eq.Prod
import Theorem.List.ProdSet__Mul_Get.eq.MulProd_Mul_Prod.of.GtLength
import Theorem.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLengthTail
import Theorem.List.Prod.eq.Mul_ProdTail.of.GtLength_0
import Theorem.List.EraseIdxAppend.eq.Append_EraseIdx
import Theorem.List.InsertIdxAppend.eq.Append_InsertIdx.of.LeLength
import Theorem.List.SwapAppend.eq.Append_Swap.of.LeLength.LeLength
import Theorem.List.ProdSwap.eq.Prod
import Theorem.List.Rotate_Mod.eq.Rotate
import Theorem.List.EqPermute
import Theorem.List.EqTake.of.LeLength
import Theorem.List.Drop.eq.Nil.of.LeLength
import Theorem.List.LengthDrop.eq.SubLength
import Theorem.List.Swap.eq.PermutePermute.of.Lt.GtLength
import Theorem.List.Swap.of.Prod.eq.IteGt
import Theorem.List.EqEraseIdx.of.LeLength
import Theorem.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Theorem.List.ProdPermute.eq.MulProd_ProdAppend
import Theorem.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Theorem.List.ProdPermute__Neg.eq.MulProd_ProdDrop
import Theorem.List.ProdTake_1.eq.HeadD_1
import Theorem.List.Rotate.eq.AppendDrop__Take
import Instance.Data.Tensor.Defs
open Bool Nat Int List Lean


def Tensor.toVector (X : Tensor α s) : List.Vector (Tensor α s.tail) (s.headD 1) :=
  cast (by rw [ProdTake_1.eq.HeadD_1]) ((X.data.splitAt 1).map fun v : List.Vector α (s.drop 1).prod => (⟨cast (by simp) v⟩ : Tensor α s.tail))

