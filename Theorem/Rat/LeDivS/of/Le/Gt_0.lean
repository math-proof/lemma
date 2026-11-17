module

public import Theorem.Nat.Ge.of.Gt
public import Theorem.Rat.LeDivS.of.Le.Ge_0

public section

open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| path | Rat.LeDivS.of.Le.Gt_0 |
| comm 2 | Rat.GeDivS.of.Ge.Gt_0 |
-/
@[comm 2]
public theorem Rat.LeDivS.of.Le.Gt_0
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x > 0) :
-- imply
  a / x ≤ b / x := by
-- proof
  apply LeDivS.of.Le.Ge_0 h₀
  apply Ge.of.Gt h₁


-- created on 2024-11-25
-- updated on 2025-12-11
