import torch.Tensor.Basic
import torch.Tensor.sum
import torch.Tensor.unsqueeze
import torch.Tensor.repeat
import torch.Tensor.permute
open List Tensor

/--
[bmm](https://docs.pytorch.org/docs/stable/generated/torch.bmm.html)
-/
def Tensor.bmm [Mul α] [Add α] [Zero α] (A : Tensor α (batch_size ++ [m, k])) (B : Tensor α (batch_size ++ [k, n])) : Tensor α (batch_size ++ [m, n]) :=
  let A : Tensor α (batch_size ++ [m, 1, k]) := cast (by simp_all [InsertIdxAppend.eq.Append_InsertIdx]) (A.unsqueeze (batch_size.length + 1))
  let A : Tensor α (batch_size ++ [m, n, k]) := cast (by simp) (A.repeat ⟨batch_size.length + 1, by simp⟩ n)
  let B : Tensor α (batch_size ++ [n, k]) := cast (by simp_all [SwapAppend.eq.Append_Swap.of.LeLength.LeLength]) B.T
  let B : Tensor α (batch_size ++ [1, n, k]) := cast (by simp_all [InsertIdxAppend.eq.Append_InsertIdx.of.LeLength]) (B.unsqueeze batch_size.length)
  let B : Tensor α (batch_size ++ [m, n, k]) := cast (by simp) (B.repeat ⟨batch_size.length, by simp⟩ m)
  cast (by simp_all [EraseIdxAppend.eq.Append_EraseIdx]) ((A * B).sum (batch_size.length + 2))
