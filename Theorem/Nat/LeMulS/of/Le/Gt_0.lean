module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.Ge.of.Gt
public import Theorem.Nat.LeMulS.of.Le.Ge_0

public section

open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeMulS.of.Le.Gt_0 |
| comm 2 | Nat.GeMulS.of.Ge.Gt_0 |
-/
@[path, comm 2]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x > 0) :
-- imply
  a * x ≤ b * x :=
-- proof
  LeMulS.of.Le.Ge_0 h₀ (Ge.of.Gt h₁)


-- created on 2024-07-01
