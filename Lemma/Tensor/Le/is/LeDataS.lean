import sympy.tensor.Basic
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Le.is.LeDataS |
| comm | Tensor.LeDataS.is.Le |
| mp | Tensor.LeDataS.of.Le |
| mpr | Tensor.Le.of.LeDataS |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α]
-- given
  (A B : Tensor α s) :
-- imply
  A ≤ B ↔ A.data ≤ B.data := by
-- proof
  cases A
  cases B
  simp only [LE.le]


-- created on 2026-07-26
