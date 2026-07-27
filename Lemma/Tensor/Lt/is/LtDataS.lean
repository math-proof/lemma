import sympy.tensor.Basic
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Lt.is.LtDataS |
| comm | Tensor.LtDataS.is.Lt |
| mp | Tensor.LtDataS.of.Lt |
| mpr | Tensor.Lt.of.LtDataS |
-/
@[main, comm, mp, mpr]
private lemma main
  [LT α]
-- given
  (A B : Tensor α s) :
-- imply
  A < B ↔ A.data < B.data := by
-- proof
  cases A
  cases B
  simp only [LT.lt]


-- created on 2026-07-26
