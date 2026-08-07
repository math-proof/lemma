import stdlib.SEq
import sympy.tensor.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.MapCast.as.Map.of.Eq |
| comm 1 | Tensor.Map.as.MapCast.of.Eq |
| cast | Tensor.MapCast.eq.Cast_Map.of.Eq |
-/
@[main, comm 1, cast]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (f : α → β) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).map f ≃ X.map f := by
-- proof
  subst h_s
  rfl


-- created on 2026-08-07
