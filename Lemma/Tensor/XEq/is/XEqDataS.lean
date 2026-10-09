import sympy.Basic
import torch.functions


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.XEq.is.XEqDataS |
| comm | Tensor.XEqDataS.is.XEq |
| mp | Tensor.XEqDataS.of.XEq |
| mpr | Tensor.XEq.of.XEqDataS |
-/
@[path, comm, mp, mpr]
private lemma main
  [XEq α]
-- given
  (A B : Tensor α s) :
-- imply
  A ≈ B ↔ A.data ≈ B.data := by
-- proof
  cases A
  cases B
  aesop


-- created on 2025-12-23
