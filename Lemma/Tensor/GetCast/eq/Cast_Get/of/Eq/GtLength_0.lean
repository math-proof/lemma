import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.Lt_Length.of.GtLength_0
open Tensor Bool


@[main]
private lemma main
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have h := congrArg (Tensor α) h₁
  have := Lt_Length.of.GtLength_0 h₀ X i
  have := Lt_Length.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩
  (cast h X)[i] = cast (by rw [h₁]) X[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetCast.as.Get.of.Eq.GtLength_0 h₀ h₁ X i


@[main]
private lemma fin
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have h := congrArg (Tensor α) h₁
  (cast h X).get ⟨i, Lt_Length.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩⟩ = cast (by rw [h₁]) (X.get ⟨i, Lt_Length.of.GtLength_0 h₀ X i⟩) := by
-- proof
  apply main h₀ h₁ X i


-- created on 2025-07-04
