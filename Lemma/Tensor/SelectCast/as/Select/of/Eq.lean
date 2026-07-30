import stdlib.SEq
import sympy.tensor.tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.SelectCast.as.Select.of.Eq |
| cast | Tensor.SelectCast.eq.Cast_Select.of.Eq |
-/
@[main, cast]
private lemma main
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (d : Fin s.length)
  (i : Fin s[d]) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).select ⟨d, by grind⟩ ⟨i, by aesop⟩ ≃ X.select d i := by
-- proof
  aesop


-- created on 2025-10-05
