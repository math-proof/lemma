import Theorem.List.Append.of.Eq
import Theorem.List.AppendAppend.eq.Append_Append
import Theorem.List.Drop.eq.ListGet.of.GtLength_0
import Theorem.List.DropLast.eq.Take_SubLength_1
import Theorem.List.EqAppendTake__ListGet.of.GeLength_2
import Theorem.List.EraseIdx.eq.Append_Drop_Add_1
import Theorem.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
import Theorem.List.ZipWith_Append.eq.AppendZipWithS
import Theorem.List.ZipWith__Append.eq.AppendZipWithS
import Instance.Data.Tensor.Tensor.Part2
import Def.LinearAlgebra.Matrix.Matmul
open List Tensor


/--
Tensor matrix product (`⬝ᵥ`).
-/
instance [Mul α] [Add α] [Zero α] : Dot (Tensor α s) (Tensor α s') (Tensor α (matmul_shape s s')) := ⟨einsum⟩

