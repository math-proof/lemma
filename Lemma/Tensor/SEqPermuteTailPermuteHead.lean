import Lemma.Tensor.SEqPermuteTailPermuteHead.of.Ne_Nil
import Lemma.Tensor.SEqPermuteTail_0
import Lemma.Tensor.SEqPermuteHead_0
open Tensor


@[main]
private lemma main
-- given
  (X : Tensor α s) :
-- imply
  (X.permuteHead s.length).permuteTail s.length ≃ X := by
-- proof
  by_cases h_s : s = []
  ·
    subst h_s
    simp
    have := SEqPermuteTail_0 (X.permuteHead 0)
    apply SEq.trans this
    apply SEqPermuteHead_0
  ·
    apply SEqPermuteTailPermuteHead.of.Ne_Nil h_s


-- created on 2025-10-20
