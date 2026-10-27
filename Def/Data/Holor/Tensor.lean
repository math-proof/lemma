import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Select
import Def.Data.Holor.Resize
import Def.Data.Holor.Shape
import Def.Data.Holor.Sum
import Def.Data.Holor.Mean
import Def.Data.Holor.Bmm
import Def.Data.Holor.Prod
import Def.Data.Holor.Reshape
import Def.Data.Holor.Unsqueeze
import Def.Data.Holor.Repeat
import Notation.Data.Holor.Permute
import Def.Data.Holor.Item
import Def.Data.Holor.HStack
import Lemma.Bool.HEq.of.All_HEq
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.GtVal_0.of.Ne_0
import Lemma.Nat.LtSubS_1.of.Lt.Ne_0
import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.EqAddMulDiv
import Lemma.Int.LtToNatAdd_Mul_DivSub1Sign_2.of.In_IcoNeg
import Lemma.List.MapEnumerate.eq.Cons_MapEnumerate.of.All_Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.LengthDrop_1.ge.Sub_1.of.GeLength.Gt_1
import Lemma.List.GtLength_0.of.Cons.in.CartesianProduct
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.LengthTake.gt.Zero.of.LengthTake.gt.Zero
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.Sub_1.lt.LengthTail.of.In_Ioo0Length
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.GtLength
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.In_CartesianProduct.of.In_CartesianProductCons
import Lemma.List.Lt.of.In_CartesianProductCons
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
open Bool Nat Int List Tensor


def Tensor.get (X : Tensor α s) (i : Fin X.length) : Tensor α s.tail :=
  have h_i := i.isLt
  have h_GtLength_0 := GtLength_0.of.GtLength_0 (X := X) (by linarith)
  have h_EqHeadD := HeadD.eq.Get_0.of.GtLength_0 h_GtLength_0 1
  have := Get_0.eq.Length.of.GtLength_0 h_GtLength_0 X
  X.toVector[i]

