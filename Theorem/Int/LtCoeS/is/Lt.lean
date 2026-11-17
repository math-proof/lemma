module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.LtCoeS.is.Lt |
| comm | Int.Lt.is.LtCoeS |
| mp   | Int.Lt.of.LtCoeS |
| mpr  | Int.LtCoeS.of.Lt |
| mp.comm | Int.Gt.of.GtCoeS |
| mpr.comm | Int.GtCoeS.of.Gt |
| comm.is | Int.GtCoeS.is.Gt |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Int.LtCoeS.is.Lt
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Int.cast_lt



public theorem Int.GtCoeS.of.Gt
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ} (h : a > b) : (a : R) > (b : R) :=
  (Int.LtCoeS.is.Lt b a).mpr h

public theorem Int.Gt.of.GtCoeS
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
  {a b : ℤ} (h : (a : R) > (b : R)) : a > b :=
  (Int.LtCoeS.is.Lt b a).mp h

-- created on 2025-10-16
