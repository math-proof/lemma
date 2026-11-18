module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Bool.Eq.of.HEq
public import Theorem.Bool.HEq.is.EqCast.of.Eq

public section

open Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.EqCast.of.HEq |
| comm 1 | Bool.Eq_Cast.of.HEq |
-/
@[comm 1]
public theorem Bool.EqCast.of.HEq
  {a : α}
  {b : β}
-- given
  (h : HEq a b) :
-- imply
  cast (Eq.of.HEq h) a = b :=
-- proof
  EqCast.of.HEq.Eq (Eq.of.HEq h) h


public theorem Bool.Eq_Cast.of.HEq
  {a : α} {b : β}
  (h : HEq a b) :
  a = cast (Eq.of.HEq (HEq.symm h)) b :=
  (Bool.EqCast.of.HEq (HEq.symm h)).symm

-- created on 2025-07-16
