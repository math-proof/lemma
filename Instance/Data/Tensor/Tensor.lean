import Def.Data.Tensor.Defs.Part4
import Def.Data.Tensor.Select
import Def.Data.Tensor.Resize
import Def.Data.Tensor.Shape
import Def.Data.Tensor.Sum
import Def.Data.Tensor.Mean
import Def.Data.Tensor.Bmm
import Def.Data.Tensor.Prod
import Def.Data.Tensor.Reshape
import Def.Data.Tensor.Unsqueeze
import Def.Data.Tensor.Repeat
import Notation.Data.Tensor.Permute
import Def.Data.Tensor.Item
import Def.Data.Tensor.HStack
import Theorem.Bool.HEq.of.All_HEq
import Theorem.Nat.Le_Sub_1.of.Lt
import Theorem.Nat.LtAddS.is.Lt
import Theorem.Nat.GtVal_0.of.Ne_0
import Theorem.Nat.LtSubS_1.of.Lt.Ne_0
import Theorem.Nat.Ge_1.of.Gt_0
import Theorem.Nat.EqAddSub.of.Ge
import Theorem.Nat.EqAddMulDiv
import Theorem.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Theorem.List.HeadD.eq.Get_0.of.GtLength_0
import Theorem.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Theorem.List.GtLength_0.of.Cons.in.CartesianProduct
import Theorem.List.EqCons_Tail.of.GtLength_0
import Theorem.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Theorem.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Theorem.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
import Theorem.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Theorem.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Theorem.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Theorem.List.In_CartesianProduct.of.In_CartesianProductCons
import Theorem.List.Lt.of.In_CartesianProductCons
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength_0.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.DataDiv.eq.DivDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.DataInv.eq.InvData
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength
import Lemma.Tensor.EqLength
import Lemma.Tensor.LengthMap.eq.Length
import Lemma.Tensor.Eq.is.Item
import Def.Data.Tensor.Tensor
open Bool Nat Int List Tensor


instance : GetElem (Tensor α s) ℕ (Tensor α s.tail) fun X i => i < X.length where
  getElem X i h := X.get ⟨i, h⟩

instance : GetElem (Tensor α s) ℤ (Tensor α s.tail) fun X i => i ∈ Ico (-X.length : ℤ) X.length where
  getElem X i h :=
    have := LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg h
    let i := Slice.Add_Mul_DivSub1Sign_2 X.length i
    X[i.toNat]

instance : GetElem (Tensor α s) (Tensor ℕ []) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i h := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ []) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℕ [n].tail) (Tensor α s.tail) fun X i => i.data[0] < X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α s) (Tensor ℤ [n].tail) (Tensor α s.tail) fun X i => i.data[0] ∈ Ico (-X.length : ℤ) X.length where
  getElem X i _ := X[i.data[0]]

instance : GetElem (Tensor α (m :: s)) (Tensor (Fin k) [n].tail) (Tensor α s) fun _ _ => k ≤ m where
  getElem X i h := X[i.data[0]]

