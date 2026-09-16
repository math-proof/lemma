import torch.Tensor.Basic
import Lemma.List.MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength
open List Tensor

/--
[select](https://docs.pytorch.org/docs/stable/generated/torch.Tensor.select.html)
-/
def Tensor.select (X : Tensor α s) (offset : Fin s.length) (i : Fin s[offset]) : Tensor α (s.eraseIdx offset) :=
  ⟨cast (congrArg (List.Vector α) (MulLengthSlice.eq.ProdEraseIdx.of.GtGet.GtLength.simp offset.isLt i.isLt)) ((X.data.splitAt (offset + 1))[i : (s.take (offset + 1)).prod : s[offset]].flatten)⟩
