import torch.Tensor.Basic
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.MapData.eq.DataMap |
| comm | Tensor.DataMap.eq.MapData |
-/
@[path, comm]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s) :
-- imply
  X.data.map f = (X.map f).data := by
-- proof
  rfl


-- created on 2026-07-29
