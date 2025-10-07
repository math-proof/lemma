import sympy.tensor.tensor
import Lemma.Bool.SEq.of.Eq
import Lemma.Logic.SEqCast.of.Eq
import Lemma.Logic.SEq.of.SEq.SEq
open Logic Bool


@[main]
private lemma main
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h₀ : s = s')
  (h₁ : Y = cast (by rw [h₀]) X) :
-- imply
  Y ≃ X := by
-- proof
  let X' : Tensor α s' := cast (by rw [h₀]) X
  have h_X : X' = cast (by rw [h₀]) X := rfl
  rw [← h_X] at h₁
  have h₁ := SEq.of.Eq h₁
  apply SEq.of.SEq.SEq h₁
  apply SEq.symm
  apply SEqCast.of.Eq h₀ X


-- created on 2025-06-29
