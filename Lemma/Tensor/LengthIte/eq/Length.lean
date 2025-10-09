import Lemma.Tensor.EqLengthS
open Tensor


@[main]
private lemma left
  [Decidable p]
-- given
  (A B : Tensor α s) :
-- imply
  (if p then
    A
  else
    B).length = A.length := by
-- proof
  split_ifs with h
  ·
    rfl
  ·
    apply EqLengthS B A


@[main]
private lemma main
  [Decidable p]
-- given
  (A B : Tensor α s) :
-- imply
  (if p then
    A
  else
    B).length = B.length := by
-- proof
  split_ifs with h
  ·
    apply EqLengthS A B
  ·
    rfl


-- created on 2025-10-09
