import Lemma.Set.Ge.Le.of.In_Icc
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.LeAddS.is.Le
import Lemma.Set.In_Icc.of.Le.Ge
open Set Nat


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b)
  (t : α):
-- imply
  x + t ∈ Icc (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := Ge.Le.of.In_Icc h
  have h₀ := GeAddS.of.Ge t h₀
  have h₁ := LeAddS.of.Le t h₁
  apply In_Icc.of.Le.Ge h₁ h₀


-- created on 2025-04-30
-- updated on 2025-05-12
