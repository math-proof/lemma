import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.GtLength.of.GtLength_0
open Tensor


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
  subst h₁
  rfl


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
  subst h₁
  rfl


-- created on 2025-07-04
-- updated on 2025-07-17
