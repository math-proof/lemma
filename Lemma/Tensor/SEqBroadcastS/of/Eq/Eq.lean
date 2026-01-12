import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.SEqBroadcastS.of.SEq.Eq
open Tensor Bool


@[main]
private lemma main
  [Mul α] [Zero α] [Add α]
  {A B : Tensor α s}
-- given
  (h_dvd : s.prod ∣ s_A.prod)
  (h_s : s_A = s_B)
  (h : A = B) :
-- imply
  A.broadcast s_A h_dvd ≃ B.broadcast s_B (by rwa [← h_s]) := by
-- proof
  apply SEqBroadcastS.of.SEq.Eq _ h_s
  apply SEq.of.Eq h


-- created on 2026-01-12
