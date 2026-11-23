module

public import Theorem.List.Append.of.Eq
public import Theorem.List.AppendAppend.eq.Append_Append
public import Theorem.List.Drop.eq.ListGet.of.GtLength_0
public import Theorem.List.DropLast.eq.Take_SubLength_1
public import Theorem.List.EqAppendTake__ListGet.of.GeLength_2
public import Theorem.List.EraseIdx.eq.Append_Drop_Add_1
public import Theorem.List.EraseIdxAppend.eq.Append_EraseIdx.of.LeLength
public import Theorem.List.ZipWith_Append.eq.AppendZipWithS
public import Theorem.List.ZipWith__Append.eq.AppendZipWithS
public import Instance.Data.Tensor.Tensor.Part2
public import Def.LinearAlgebra.Matrix.Matmul
@[expose] public section

open List Tensor


/--
Tensor matrix product (`⬝ᵥ`).
-/
instance [Mul α] [Add α] [Zero α] : Dot (Tensor α s) (Tensor α s') (Tensor α (matmul_shape s s')) := ⟨einsum⟩

