import Lemma.List.Append.of.Eq
import Lemma.List.AppendAppend.eq.Append_Append
import Lemma.List.Drop.eq.ListGet.of.GtLength_0
import Lemma.List.DropLast.eq.Take_SubLength_1
import Lemma.List.EqAppendTake__ListGet.of.GeLength_2
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Lemma.List.ZipWith_Append.eq.AppendZipWithS
import Lemma.List.ZipWith__Append.eq.AppendZipWithS
import Instance.Data.Holor.Tensor.Part2
import Def.LinearAlgebra.Matrix.Matmul
open List Tensor


/--
Tensor matrix product (`@`).
-/
instance [Mul α] [Add α] [Zero α] : Dot (Tensor α s) (Tensor α s') (Tensor α (matmul_shape s s')) := ⟨einsum⟩

