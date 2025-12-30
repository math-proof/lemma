import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
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
  have h := congrArg (Tensor α) h₁
  have := GtLength.of.GtLength_0 h₀ X ⟨i, by grind⟩
  have := GtLength.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩
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
  have h := congrArg (Tensor α) h₁
  (cast h X).get ⟨i, GtLength.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩⟩ = cast (by rw [h₁]) (X.get ⟨i, GtLength.of.GtLength_0 h₀ X ⟨i, by grind⟩⟩) :=
-- proof
  main h₀ h₁ h_i X

-- created on 2025-07-04
