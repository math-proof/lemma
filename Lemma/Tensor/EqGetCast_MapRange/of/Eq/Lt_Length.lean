import Lemma.Tensor.EqGetCast_MapRange.of.Eq
open Tensor


@[main]
private lemma main
-- given
  (h₀ : i < n)
  (h₁ : s = s')
  (f : Fin n → Tensor α s) :
-- imply
  have h : List.Vector (Tensor α s) n = List.Vector (Tensor α s') n := by rw [h₁]
  (cast h ((List.Vector.range n).map f))[i] ≃ f ⟨i, h₀⟩ := by
-- proof
  have := EqGetCast_MapRange.of.Eq h₁ f ⟨i, h₀⟩
  simp_all


-- created on 2025-06-29
