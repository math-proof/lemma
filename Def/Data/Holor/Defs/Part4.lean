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
import Instance.Data.Holor.Defs.Part3
open Bool Nat Int List Lean


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

