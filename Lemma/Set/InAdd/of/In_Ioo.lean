import Lemma.Nat.GtAddS.is.Gt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Set.In_Ioo.of.Lt.Gt
open Set Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x a b : α}
-- given
  (h : x ∈ Ioo a b)
  (t : α) :
-- imply
  x + t ∈ Ioo (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  have h₀ := GtAddS.of.Gt t h₀
  have h₁ := LtAddS.of.Lt t h₁
  apply In_Ioo.of.Lt.Gt h₁ h₀


-- created on 2025-08-02
