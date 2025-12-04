import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Tensor.KeepdimNeg.eq.NegKeepdim
import Lemma.Tensor.SoftmaxAdd_Keepdim.eq.Softmax
open Tensor Int


@[main]
private lemma main
  [ExpRing α]
  {d : ℕ}
-- given
  (X : Tensor α s)
  (δ : Tensor α (s.eraseIdx d)) :
-- imply
  (X - δ.keepdim).softmax d = X.softmax d := by
-- proof
  have := SoftmaxAdd_Keepdim.eq.Softmax X (-δ)
  rw [KeepdimNeg.eq.NegKeepdim] at this
  rwa [Add_Neg.eq.Sub] at this


-- created on 2025-12-04
