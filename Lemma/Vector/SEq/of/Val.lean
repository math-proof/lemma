import stdlib.SEq
import Lemma.Vector.Eq.of.Val
import Lemma.Bool.UFn.of.Eq
open Vector Bool


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a.val = b.val) :
-- imply
  a ≃ b := by
-- proof
  have h_length := UFn.of.Eq h List.length
  simp at h_length
  constructor
  .
    assumption
  .
    subst h_length
    simp
    apply Eq.of.Val h


-- created on 2025-07-25
