import Initialize.Tactic.Attr.Basic
import Theorem.Lean.Meta.Expr


/--
| attributes | lemma |
| :---: | :---: |
| path | Int.GeCeil |
| comm | Int.Le_Ceil |
-/
@[path, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ ≥ x :=
-- proof
  Int.le_ceil x


-- created on 2018-05-10
-- updated on 2026-11-17
