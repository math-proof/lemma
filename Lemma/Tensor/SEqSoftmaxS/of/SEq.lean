import sympy.tensor.functions
import Lemma.Bool.SEqBFnS.of.SEq
open Bool


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
  apply SEqBFnS.of.SEq h (fun (s : List ℕ) (X : Tensor α s) => X.softmax i)


-- created on 2025-10-31
