module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs.Part4

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Eq.is.EqDataS |
| comm | Tensor.EqDataS.is.Eq |
| mp | Tensor.EqDataS.of.Eq |
| mpr | Tensor.Eq.of.EqDataS |
-/
@[comm, mp, mpr]
public theorem Tensor.Eq.is.EqDataS
-- given
  (A B : Tensor α s) :
-- imply
  A = B ↔ A.data = B.data := by
-- proof
  cases A
  cases B
  simp



public theorem Tensor.Eq.of.EqDataS
  (A B : Tensor α s) (h : A.data = B.data) :
  A = B :=
  (Tensor.Eq.is.EqDataS A B).mpr h

-- created on 2025-05-06
