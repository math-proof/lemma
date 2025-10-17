import sympy.tensor.Basic
import Lemma.Tensor.EqTFnS.of.Eq.Lt_Length
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (h_d : d < s.length)
  (k : ℕ) :
-- imply
  A.repeat k ⟨d, h_d⟩ ≃ B.repeat k ⟨d, by rwa [← h.left]⟩ := by
-- proof
  apply EqTFnS.of.Eq.Lt_Length h_d h _ (fun (s : List ℕ) (d : Fin s.length) (X : Tensor α s) => X.repeat k d)


-- created on 2025-07-13
