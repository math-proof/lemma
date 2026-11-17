module

public import Initialize.Tactic.Attr.Basic
public import Theorem.Lean.Meta.Expr

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LtMulS.of.Gt_0.Lt |
| comm | Nat.GtMulS.of.Gt_0.Gt |
-/
@[comm 1]
public theorem Nat.LtMulS.of.Gt_0.Lt
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a < b) :
-- imply
  x * a < x * b :=
-- proof
  mul_lt_mul_of_pos_left h₁ h₀


-- created on 2025-11-07
