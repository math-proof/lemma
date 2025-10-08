import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.Sub.eq.Zero.of.Le
open Algebra Nat


@[main]
private lemma main
-- given
  (h : a < b) :
-- imply
  a - b = 0 := by
-- proof
  have h := Le.of.Lt h
  apply Sub.eq.Zero.of.Le h


-- created on 2025-05-14
