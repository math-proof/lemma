import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Le.of.LtSub_1
import Lemma.Nat.Sub.eq.Zero
import Lemma.Nat.NotGt.is.Le
import Lemma.Nat.NotOdd.is.Even
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Nat.EqAddSub_1.of.Lt_0
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n is odd) :
-- imply
  n = n - 1 + 1 := by
-- proof
  if h_n : n > 0 then
    rw [EqAddSub.of.Ge]
    apply Ge.of.Gt_Sub_1
    rwa [Sub.eq.Zero]
  else
    have h_n := Le.of.NotGt h_n
    if h_0 : n = 0 then
      rw [h_0] at h
      have h_0 : (0 : Z) is even := by
        simp
      rw [Even.is.NotOdd] at h_0
      contradiction
    else
      have h_n := Lt.of.Le.Ne h_0 h_n
      apply EqAddSub_1.of.Lt_0 h_n


-- created on 2025-08-13
