import Lemma.Tensor.SEqPermuteHead_0
import Lemma.Tensor.SEqPermuteHead_1
open Tensor


@[main]
private lemma main
-- given
  (h : n ≤ 1)
  (X : Tensor α s) :
-- imply
  X.permuteHead n ≃ X := by
-- proof
  match n with
  | 0 =>
    simp
    apply SEqPermuteHead_0
  | n + 1 =>
    simp_all
    subst n
    simp
    apply SEqPermuteHead_1


-- created on 2025-11-01
