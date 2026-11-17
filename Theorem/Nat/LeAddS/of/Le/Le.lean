module

public import Theorem.Nat.LeAddS.is.Le
public import Theorem.Nat.Le.of.Le.Le

public section

open Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.LeAddS.of.Le.Le |
| comm 3 | Nat.GeAddS.of.Ge.Ge |
-/
@[comm 3]
public theorem Nat.LeAddS.of.Le.Le
  [Add α]
  [Preorder α]
  [AddRightMono α] [AddLeftMono α]
  {a b x y : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ y) :
-- imply
  a + x ≤ b + y := by
-- proof
  have h₂ := LeAddS.of.Le x h₀
  have h₃ := LeAddS.of.Le.left b h₁
  apply Le.of.Le.Le h₂ h₃


-- created on 2024-11-25
-- updated on 2025-04-30
