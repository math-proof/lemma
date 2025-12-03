import Lemma.Vector.SoftmaxAdd.eq.Softmax
import Lemma.Vector.Sub.eq.Add_Neg
open Vector


@[main]
private lemma main
  [ExpRing α]
-- given
  (x : List.Vector α n)
  (δ : α) :
-- imply
  (x - δ).softmax = x.softmax := by
-- proof
  have := SoftmaxAdd.eq.Softmax x (-δ)
  rwa [Add_Neg.eq.Sub] at this


-- created on 2025-12-03
