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
open Bool Nat Int List Lean


/--
the concept of a Tensor is a generalization of a matrix, like the Tensor concept in pytorch / tensorflow
the declaration syntax is similar
```lean
-- in lean:
import Instance.Data.Holor.Tensor.Part2
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

