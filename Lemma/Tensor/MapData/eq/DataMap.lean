import sympy.tensor.Basic
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapData.eq.DataMap |
| comm | Tensor.DataMap.eq.MapData |
-/
@[main, comm]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s) :
-- imply
  X.data.map f = (X.map f).data := by
-- proof
  rfl


-- created on 2026-07-29
