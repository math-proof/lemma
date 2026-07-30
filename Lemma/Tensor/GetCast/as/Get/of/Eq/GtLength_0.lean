import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.GtLength.of.GtLength_0
open Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetCast.as.Get.of.Eq.GtLength_0 |
| fin | Tensor.GetCast.as.Get.of.Eq.GtLength_0.fin |
| cast | Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0 |
| cast.fin | Tensor.GetCast.eq.Cast_Get.of.Eq.GtLength_0.fin |
-/
@[main, fin, cast, cast.fin]
private lemma main
  {s s' : List ℕ}
-- given
  (h₀ : s.length > 0)
  (h₁ : s = s')
  (X : Tensor α s)
  (i : Fin s[0]) :
-- imply
  have h := congrArg (Tensor α) h₁
  have := GtLength.of.GtLength_0 h₀ X i
  have := GtLength.of.GtLength_0 (h₁ ▸ h₀) (cast h X) ⟨i, by grind⟩
  (cast h X)[i] ≃ X[i] := by
-- proof
  aesop


@[main, fin, cast, cast.fin]
private lemma right
  {s : List ℕ}
-- given
  (h₀ : s'.length > 0)
  (h₁ : s = s')
  (X : Tensor α s)
  (i : Fin s'[0]) :
-- imply
  have X' := cast (congrArg (Tensor α) h₁) X
  have := GtLength.of.GtLength_0 h₀ X' i
  have := GtLength.of.GtLength_0 (h₁ ▸ h₀) X ⟨i, by grind⟩
  X'[i] ≃ X[i] := by
-- proof
  aesop


-- created on 2025-07-04
-- updated on 2025-07-17
