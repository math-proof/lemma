import Lemma.Tensor.SEqBFnS.of.SEq
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.sum i ≃ B.sum i := by
-- proof
  apply SEqBFnS.of.SEq h _ (fun (s : List ℕ) (X : Tensor α s) => X.sum i)


-- created on 2025-10-31
