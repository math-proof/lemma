import Lemma.Tensor.MinDivLengthData.eq.ProdTail.of.GtLength_0
open Tensor


@[main]
private lemma main
-- given
  (h₀ : s.length > 0)
  (h₁ : i < s[0])
  (X : Tensor α s) :
-- imply
  X.data.length / s[0] ⊓ (s.prod - i * (X.data.length / s[0])) = s.tail.prod := by
-- proof
  let i' : Fin s[0] := ⟨i, h₁⟩
  have h_i : i' = i := rfl
  have := MinDivLengthData.eq.ProdTail.of.GtLength_0 h₀ X i'
  simp_all


-- created on 2025-06-29
