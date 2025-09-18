import sympy.tensor.tensor
import Lemma.Tensor.Lt_Length.of.Eq
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B) :
-- imply
  ∀ i : Fin A.length, A.get i ≃ B.get ⟨i, Lt_Length.of.Eq h i⟩ := by
-- proof
  let ⟨h_s, h⟩ := h
  intro i
  subst h_s
  have := HEq.eq h
  aesop


-- created on 2025-07-24
