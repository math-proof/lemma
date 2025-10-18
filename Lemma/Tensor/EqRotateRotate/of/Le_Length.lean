import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.Tensor.Permute.eq.Ite


@[main]
private lemma main
-- given
  (h : i ≤ s.length)
  (X : Tensor α s) :
-- imply
  (X.rotate i).rotate (s.length - i) ≃ X := by
-- proof
  sorry


-- created on 2025-10-18
