import sympy.functions.elementary.integers
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Ge.of.Gt_Sub_1
import Lemma.Algebra.Sub.eq.Zero
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.NotOdd.is.Even
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Algebra.EqAddSub_1.of.Lt_0
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n is odd) :
-- imply
  n = n - 1 + 1 := by
-- proof
  by_cases h_n : n > 0
  · 
    rw [EqAddSub.of.Ge]
    apply Ge.of.Gt_Sub_1
    rwa [Sub.eq.Zero.int]
  · 
    have h_n := Le.of.NotGt h_n
    by_cases h_0 : n = 0
    · 
      rw [h_0] at h
      have h_0 : (0 : Z) is even := by 
        simp
      rw [Even.is.NotOdd] at h_0
      contradiction
    · 
      have h_n := Lt.of.Le.Ne h_0 h_n
      apply EqAddSub_1.of.Lt_0 h_n


-- created on 2025-08-13
