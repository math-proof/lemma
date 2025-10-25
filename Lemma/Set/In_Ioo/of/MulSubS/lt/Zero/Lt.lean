import Lemma.Int.Mul.lt.Zero.is.OrAndSLt_0Gt_0
import Lemma.Int.Lt.of.Sub.lt.Zero
import Lemma.Int.Sub.gt.Zero.is.Gt
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Nat.NotLt.of.Gt
import Lemma.Set.In_Ioo.of.Gt.Lt
open Set Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : (x - a) * (x - b) < 0)
  (h₁ : a < b) :
-- imply
  x ∈ Ioo a b := by
-- proof
  have h_Or := OrAndSLt_0Gt_0.of.Mul.lt.Zero h₀
  rcases h_Or with h_And | h_And
  ·
    let ⟨h_Lt, h_Gt⟩ := h_And
    have h_Lt := Lt.of.Sub.lt.Zero h_Lt
    have h_Gt := Gt.of.Sub.gt.Zero h_Gt
    have := Gt.of.Gt.Gt h_Lt h_Gt
    have := NotLt.of.Gt this
    contradiction
  ·
    let ⟨h_Lt, h_Gt⟩ := h_And
    have h_Lt := Lt.of.Sub.lt.Zero h_Lt
    have h_Gt := Gt.of.Sub.gt.Zero h_Gt
    apply In_Ioo.of.Gt.Lt h_Gt h_Lt


-- created on 2025-03-30
