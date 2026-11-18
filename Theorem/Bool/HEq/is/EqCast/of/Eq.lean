module
public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.HEq.is.EqCast.of.Eq |
| comm | Bool.EqCast.is.HEq.of.Eq |
| mp | Bool.EqCast.of.HEq.Eq |
| mpr | Bool.HEq.of.EqCast.Eq |
-/
@[comm, mp, mpr]
public theorem Bool.HEq.is.EqCast.of.Eq
  {a : α}
  {b : β}
-- given
  (h : α = β) :
-- imply
  HEq a b ↔ cast h a = b := by
-- proof
  aesop


@[comm, mp, mpr]
public theorem Congr
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : m = n) :
-- imply
  HEq b a ↔ cast (congrArg Vector h) b = a := by
-- proof
  aesop


public theorem Bool.EqCast.of.HEq.Eq
  {a : α} {b : β}
  (h : α = β)
  (hheq : HEq a b) :
  cast h a = b :=
  (Bool.HEq.is.EqCast.of.Eq h).mp hheq

-- created on 2025-07-16
