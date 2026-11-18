module

public import Def.Data.Tensor.Defs.Part4
public import Def.Data.Tensor.Select
public import Def.Data.Tensor.Resize
public import Def.Data.Tensor.Shape
public import Def.Data.Tensor.Sum
public import Def.Data.Tensor.Mean
public import Def.Data.Tensor.Bmm
public import Def.Data.Tensor.Prod
public import Def.Data.Tensor.Reshape
public import Def.Data.Tensor.Unsqueeze
public import Def.Data.Tensor.Repeat
public import Notation.Data.Tensor.Permute
public import Def.Data.Tensor.Item
public import Def.Data.Tensor.HStack
public import Theorem.Bool.HEq.of.All_HEq
public import Theorem.Nat.Le_Sub_1.of.Lt
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.Nat.GtVal_0.of.Ne_0
public import Theorem.Nat.LtSubS_1.of.Lt.Ne_0
public import Theorem.Nat.Ge_1.of.Gt_0
public import Theorem.Nat.EqAddSub.of.Ge
public import Theorem.Nat.EqAddMulDiv
public import Theorem.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
public import Theorem.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
public import Theorem.List.HeadD.eq.Get_0.of.GtLength_0
public import Theorem.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
public import Theorem.List.GtLength_0.of.Cons.in.CartesianProduct
public import Theorem.List.EqCons_Tail.of.GtLength_0
public import Theorem.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
public import Theorem.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
public import Theorem.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
public import Theorem.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
public import Theorem.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
public import Theorem.List.GetEraseIdx.eq.Get.of.Gt.GtLength
public import Theorem.List.In_CartesianProduct.of.In_CartesianProductCons
public import Theorem.List.Lt.of.In_CartesianProductCons
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0
public import Theorem.Tensor.GtLength_0.of.GtLength_0
public import Theorem.Tensor.Eq.is.EqDataS
public import Theorem.Tensor.DataAdd.eq.AddDataS
public import Theorem.Tensor.DataMul.eq.MulDataS
public import Theorem.Tensor.DataDiv.eq.DivDataS
public import Theorem.Tensor.DataNeg.eq.NegData
public import Theorem.Tensor.DataInv.eq.InvData
public import Theorem.Tensor.EqData0'0
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength
public import Theorem.Tensor.EqLength
public import Theorem.Tensor.LengthMap.eq.Length
public import Theorem.Tensor.Eq.is.Item
public import Def.Data.Tensor.Tensor

@[expose] public section

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

