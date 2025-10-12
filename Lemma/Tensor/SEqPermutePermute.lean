import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.LengthPermute.eq.Length
import Lemma.Nat.LtVal
open List Nat


@[main]
private lemma main
  {j : Fin s.length}
-- given
  (h : i < j.val)
  (X : Tensor α s) :
-- imply
  (X.permute ⟨i, by linarith [LtVal j]⟩ (j - i)).permute ⟨j, by simp [LengthPermute.eq.Length]⟩ (i - j) ≃ X := by
-- proof
  sorry


-- created on 2025-10-12
