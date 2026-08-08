import Lemma.Hyperreal.Any_IsSt.is.NotInfinite
import sympy.core.relational
import sympy.tensor.Basic
open Hyperreal Bool Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.NotInfiniteGetData |
| fin | Tensor.NotInfiniteGetData.fin |
-/
@[main, fin]
private lemma main
-- given
  (X : Tensor ℝ s)
  (i : Fin s.prod) :
-- imply
  ¬(X : Tensor ℝ* s).data[i] → ∞ := by
-- proof
  rw [← Any_IsSt.is.NotInfinite]
  refine Exists.intro (X.data[i]) ?_
  simp [Tensor.map, GetElem.getElem]


-- created on 2026-08-08
