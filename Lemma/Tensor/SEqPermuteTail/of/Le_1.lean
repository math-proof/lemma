import Lemma.Tensor.SEqPermuteTail_0
import Lemma.Tensor.SEqPermuteTail_1
open Tensor


@[main]
private lemma main
-- given
  (h : n ≤ 1)
  (X : Tensor α s) :
-- imply
  X.permuteTail n ≃ X := by
-- proof
  match n with
  | 0 =>
    simp
    apply SEqPermuteTail_0
  | n + 1 =>
    simp_all
    subst n
    simp
    apply SEqPermuteTail_1


-- created on 2025-10-31
