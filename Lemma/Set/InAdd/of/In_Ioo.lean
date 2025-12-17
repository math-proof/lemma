import Lemma.Nat.LtAddS.is.Lt
import Lemma.Nat.LtAddS.is.Lt
import Lemma.Set.In_Ioo.is.Lt.Lt
open Set Nat


@[main]
private lemma main
  [Preorder α] [Add α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
  {x a b : α}
-- given
  (h : x ∈ Ioo a b)
  (t : α) :
-- imply
  x + t ∈ Ioo (a + t) (b + t) := by
-- proof
  let ⟨h₀, h₁⟩ := h
  apply In_Ioo.of.Lt.Lt
  .
    apply GtAddS.of.Gt t h₀
  .
    apply LtAddS.of.Lt t h₁



-- created on 2025-08-02
