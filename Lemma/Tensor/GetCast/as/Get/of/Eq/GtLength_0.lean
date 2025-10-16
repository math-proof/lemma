import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Nat.LtVal
open Tensor Nat


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
    rw [Length.eq.Get_0.of.GtLength_0 (by grind)]
    apply LtVal i
  have : i < (cast h X).length := by
    rw [Length.eq.Get_0.of.GtLength_0]
    simp [← h₁]
    rwa [← h₁]
  (cast h X)[i] ≃ X[i] := by
-- proof
  simp only [GetElem.getElem, Tensor.get]
  unfold Tensor.toVector
  constructor <;>
    aesop


-- created on 2025-07-04
-- updated on 2025-07-17
