module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.Ge0Sub.is.Le |
| comm | Int.Le.is.Ge0Sub |
| mp   | Int.Le.of.Ge0Sub |
| mpr  | Int.Ge0Sub.of.Le |
| mp.comm | Int.Ge.of.Ge0Sub |
| mpr.comm | Int.Ge0Sub.of.Ge |
| comm.is | Int.Ge0Sub.is.Ge |
-/
@[comm, mp, mpr, mp.comm, mpr.comm, comm.is]
public theorem Int.Ge0Sub.is.Le
  [AddGroup α] [LE α] [AddRightMono α]
  {x y : α} :
-- imply
  x - y ≤ 0 ↔ x ≤ y :=
-- proof
  sub_nonpos



public theorem Int.Ge0Sub.of.Le
  [AddGroup α] [LE α] [AddRightMono α]
  {x y : α} (h : x ≤ y) : x - y ≤ 0 :=
  (Int.Ge0Sub.is.Le).mpr h

-- created on 2025-03-15
-- updated on 2026-10-26
