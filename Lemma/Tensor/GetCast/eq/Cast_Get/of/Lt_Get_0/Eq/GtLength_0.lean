import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
open Tensor


@[main]
private lemma main
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h₁]
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < (cast h X).length := by
    rw [Length.eq.Get_0.of.GtLength_0]
    simpa [← h₁]
    rwa [← h₁]
  (cast h X)[i] = cast (by rw [h₁]) X[i] := by
-- proof
  let i' : Fin s[0] := ⟨i, h_i⟩
  have := GetCast.eq.Cast_Get.of.Eq.GtLength_0 h₀ h₁ X i'
  simp [i'] at this
  assumption


@[main]
private lemma fin
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (h_i : i < s[0])
  (X : Tensor α s) :
-- imply
  have h : Tensor α s = Tensor α s' := by rw [h₁]
  have : i < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  have : i < (cast h X).length := by
    rw [Length.eq.Get_0.of.GtLength_0]
    simpa [← h₁]
    rwa [← h₁]
  (cast h X).get ⟨i, by assumption⟩ = cast (by rw [h₁]) (X.get ⟨i, by assumption⟩) := by
-- proof
  apply main
  repeat assumption

-- created on 2025-07-04
