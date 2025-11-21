import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.Lt.of.Lt.Le
open Nat

/--
arguments are arranged in the constructor order of Lt
-/
@[main, comm 3]
private lemma main
  [Add α]
  [Preorder α]
  [AddLeftStrictMono α] [AddLeftMono α]
  [AddRightStrictMono α] [AddRightMono α]
  {a b x y : α}
-- given
  (h₀ : b ≤ a)
  (h₁ : y < x) :
-- imply
  b + y < a + x := by
-- proof
  have h₂ := LeAddS.of.Le x h₀
  have h₃ := LtAddS.of.Lt.left b h₁
  exact Lt.of.Lt.Le h₃ h₂


-- created on 2025-01-17
-- updated on 2025-04-30
