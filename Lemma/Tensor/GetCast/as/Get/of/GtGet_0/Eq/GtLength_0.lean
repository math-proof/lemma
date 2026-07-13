import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
open Tensor


@[main, fin, cast, cast.fin]
private lemma main
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h₁
  have := GtLength.of.GtLength_0 h₀ X ⟨i, by grind⟩
  have := GtLength.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩
  (cast h X)[i] ≃ X[i] := by
-- proof
  aesop


-- created on 2025-07-04
