import sympy.tensor.Basic
import Lemma.Tensor.EqTFnS.of.Eq.GtLength
open Tensor


@[main]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_d : s.length > d)
  (h : A ≃ B)
  (n : ℕ) :
-- imply
  A.repeat n ⟨d, h_d⟩ ≃ B.repeat n ⟨d, by rwa [← h.left]⟩ := by
-- proof
  apply EqTFnS.of.Eq.GtLength h_d h _ (fun (s : List ℕ) (d : Fin s.length) (X : Tensor α s) => X.repeat n d)


-- created on 2025-07-13
