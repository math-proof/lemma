import Lemma.Tensor.SoftmaxAdd.eq.Softmax
import Lemma.Tensor.Sub.eq.Add_Neg
open Tensor


@[main]
private lemma main
  [ExpRing α]
-- given
  (X : Tensor α s)
  (δ : α)
  (d : ℕ):
-- imply
  (X - δ).softmax d = X.softmax d := by
-- proof
  have := SoftmaxAdd.eq.Softmax X (-δ) d
  rwa [Add_Neg.eq.Sub] at this


-- created on 2025-12-04
