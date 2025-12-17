import Lemma.Set.In_Ioc.is.Lt.Le
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.LeAddS.is.Le
open Set Nat


@[main]
private lemma main
  [Preorder α] [Add α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
  {a b : α}
-- given
  (h : x ∈ Ioc a b)
  (d : α) :
-- imply
  x + d ∈ Ioc (a + d) (b + d) := by
-- proof
  have h_Lt := LtAddS.of.Lt d h.left
  have h_Le := LeAddS.of.Le d h.right
  apply In_Ioc.of.Lt.Le <;> assumption


-- created on 2025-03-02
-- updated on 2025-08-02
