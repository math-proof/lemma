import Lemma.Tensor.SEqPermuteHead_0
import Lemma.Tensor.SEqPermuteTail_0
import Lemma.Tensor.SEqPermuteHeadPermuteTail.of.Ne_Nil
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  (X.permuteTail s.length).permuteHead s.length ≃ X := by
-- proof
  if h_s : s = [] then
    subst h_s
    simp
    have := SEqPermuteHead_0 (X.permuteTail 0)
    apply SEq.trans this
    apply SEqPermuteTail_0
  else
    apply SEqPermuteHeadPermuteTail.of.Ne_Nil h_s


-- created on 2025-10-26
