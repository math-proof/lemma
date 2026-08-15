import stdlib.SEq
import sympy.tensor.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapCast.as.MapBFn.of.Eq |
| comm | Tensor.MapBFn.as.MapCast.of.Eq |
| cast.comm | Tensor.Cast_MapBFn.eq.MapCast.of.Eq |
-/
@[main, comm, cast.comm]
private lemma main
  {f : α → α → α}
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : Tensor α []) :
-- imply
  (cast (congrArg (Tensor α) h) X).map (f · n.data[0]) ≃ X.map (f · n.data[0]) := by
-- proof
  aesop


-- created on 2026-08-15
