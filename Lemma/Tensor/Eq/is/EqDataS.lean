import sympy.tensor.Basic
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Eq.is.EqDataS |
| comm | Tensor.EqDataS.is.Eq |
| mp | Tensor.EqDataS.of.Eq |
| mpr | Tensor.Eq.of.EqDataS |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor α s) :
-- imply
  A = B ↔ A.data = B.data := by
-- proof
  cases A
  cases B
  simp


-- created on 2025-05-06
