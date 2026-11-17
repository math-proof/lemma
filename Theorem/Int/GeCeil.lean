module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section

/--
| attributes | lemma |
| :---: | :---: |
| path | Int.GeCeil |
| comm | Int.Le_Ceil |
-/
@[comm]
public theorem Int.GeCeil
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ ≥ x :=
-- proof
  Int.le_ceil x


-- created on 2018-05-10
-- updated on 2026-11-17
