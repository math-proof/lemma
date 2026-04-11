import Lemma.Tensor.LengthPermuteTail.eq.Get.of.GtLength_0
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  {s : List ℕ}
  {k : ℕ}
-- given
  (h_s : s.length > 0)
  (h_k : k < s[s.length - 1])
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).get ⟨k, by rwa [LengthPermuteTail.eq.Get.of.GtLength_0 h_s]⟩ ≃ X.select ⟨s.length - 1, by grind⟩ ⟨k, by grind⟩ := by
-- proof
  sorry


-- created on 2026-04-08
-- updated on 2026-04-11
