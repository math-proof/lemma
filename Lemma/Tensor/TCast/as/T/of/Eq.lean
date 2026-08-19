import stdlib.SEq
import sympy.tensor.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.TCast.as.T.of.Eq |
| cast | Tensor.TCast.eq.Cast_T.of.Eq |
-/
@[main, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h) X)ᵀ ≃ Xᵀ := by
-- proof
  subst h
  rfl


-- created on 2026-07-11
-- updated on 2026-08-18
