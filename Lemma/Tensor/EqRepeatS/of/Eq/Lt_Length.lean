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
  (n : ℕ) :
-- imply
  A.repeat n ⟨d, h_d⟩ ≃ B.repeat n ⟨d, by rwa [← h.left]⟩ := by
-- proof
  apply EqTFnS.of.Eq.Lt_Length h_d h _ (fun (s : List ℕ) (d : Fin s.length) (X : Tensor α s) => X.repeat n d)


-- created on 2025-07-13
