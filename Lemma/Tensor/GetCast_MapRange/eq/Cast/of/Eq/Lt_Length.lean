import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.EqGetCast_MapRange.of.Eq.Lt_Length
open Tensor Bool


@[main]
private lemma main
-- given
  (h₀ : i < n)
  (h₁ : s = s')
  (f : Fin n → Tensor α s) :
-- imply
  have h : List.Vector (Tensor α s) n = List.Vector (Tensor α s') n := by rw [h₁]
  (cast h ((List.Vector.range n).map f))[i] = cast (by rw [h₁]) (f ⟨i, h₀⟩) := by
-- proof
  apply Eq_Cast.of.SEq
  apply EqGetCast_MapRange.of.Eq.Lt_Length h₀ h₁


-- created on 2025-07-15
