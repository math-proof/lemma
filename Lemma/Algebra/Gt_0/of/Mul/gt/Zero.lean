import Lemma.Algebra.Ne_0.of.Mul.gt.Zero
import Lemma.Nat.Gt_0.of.Ne_0
open Algebra Nat


@[main]
private lemma left
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  a > 0 := by
-- proof
  have := Ne_0.of.Mul.gt.Zero.left h
  apply Gt_0.of.Ne_0 this


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h : a * b > 0) :
-- imply
  b > 0 := by
-- proof
  have := Ne_0.of.Mul.gt.Zero h
  apply Gt_0.of.Ne_0 this


-- created on 2025-06-13
