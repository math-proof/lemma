import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.HEq.is.EqCast.of.Eq |
| comm | Bool.EqCast.is.HEq.of.Eq |
| mp | Bool.EqCast.of.HEq.Eq |
| mpr | Bool.HEq.of.EqCast.Eq |
-/
@[main, comm, mp, mpr]
private lemma main
  {a : α}
  {b : β}
-- given
  (h : α = β) :
-- imply
  HEq a b ↔ cast h a = b := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma Congr
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : m = n) :
-- imply
  HEq b a ↔ cast (congrArg Vector h) b = a := by
-- proof
  aesop


-- created on 2025-07-16
