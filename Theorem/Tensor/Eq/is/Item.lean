module

public import Initialize.Tactic.Attr.Basic
public import Def.Data.Tensor.Defs.Part4
public import Def.Data.Tensor.Item
public import Theorem.Tensor.Eq.is.EqDataS

public section
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Eq.is.Item |
| comm | Tensor.EqItemS.is.Eq |
| mp | Tensor.EqItemS.of.Eq |
| mpr | Tensor.Eq.of.EqItemS |
-/
@[comm, mp, mpr]
public theorem Tensor.Eq.is.Item
-- given
  (A B : Tensor α []) :
-- imply
  A = B ↔ A.item = B.item := by
-- proof
  constructor
  · intro h
    rw [h]
  · intro h
    rw [Eq.is.EqDataS]
    ext i
    have : i = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (Nat.lt_one_iff.mp i.isLt)
    subst this
    exact h


public theorem Tensor.EqItemS.is.Eq
  (A B : Tensor α []) :
  A.item = B.item ↔ A = B :=
  (Eq.is.Item A B).symm

public theorem Tensor.EqItemS.of.Eq
  (A B : Tensor α []) (h : A = B) :
  A.item = B.item :=
  (Eq.is.Item A B).mp h

public theorem Tensor.Eq.of.EqItemS
  (A B : Tensor α []) (h : A.item = B.item) :
  A = B :=
  (Eq.is.Item A B).mpr h



public theorem Tensor.Eq.of.Item
  (A B : Tensor α []) (h : A.item = B.item) :
  A = B :=
  (Eq.is.Item A B).mpr h

-- created on 2026-09-07
