import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Nat.LtVal
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Bool.EqCast.of.SEq
open Tensor Bool Nat


@[main]
private lemma main
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h₁]
  have : i < X.length := by
    rw [Length.eq.Get_0.of.GtLength_0]
    apply LtVal i
  have : i < (cast h X).length := by
    rw [Length.eq.Get_0.of.GtLength_0]
    simp [← h₁]
    rwa [← h₁]
  (cast h X)[i] = cast (by rw [h₁]) X[i] := by
-- proof
  apply Eq_Cast.of.SEq
  apply GetCast.as.Get.of.Eq.GtLength_0 h₀ h₁ X i


-- created on 2025-07-04
