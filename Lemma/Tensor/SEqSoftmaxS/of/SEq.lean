import sympy.tensor.functions
import Lemma.Tensor.SEqBFnS.of.SEq
open Tensor


@[main]
private lemma main
  [Exp α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.softmax i ≃ B.softmax i := by
-- proof
  apply SEqBFnS.of.SEq h _ (fun (s : List ℕ) (X : Tensor α s) => X.softmax i)


-- created on 2025-10-31
