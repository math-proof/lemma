import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.LengthMap.eq.Length
import torch.functions
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.GetSin.eq.SinGet |
| fin | Tensor.GetSin.eq.SinGet.fin |
| comm | Tensor.SinGet.eq.GetSin |
| fin.comm | Tensor.SinGet.eq.GetSin.fin |
-/
@[path, fin, comm, fin.comm]
private lemma main
  [Sin α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X.sin[i]'(by simp [Tensor.sin, LengthMap.eq.Length]) = X[i].sin := by
-- proof
  simp [Tensor.sin]
  exact GetMap.eq.MapGet X Sin.sin i


-- created on 2026-09-02
