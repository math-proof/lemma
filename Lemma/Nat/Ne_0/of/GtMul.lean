import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.Gt_0.of.GtMul
import Lemma.Nat.Mul
open Nat


@[main]
private lemma left
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  n ≠ 0 := by
-- proof
  have := Gt_0.of.GtMul.left h
  omega


@[main]
private lemma main
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  m ≠ 0 := by
-- proof
  rw [Mul.comm] at h
  apply left h


-- created on 2026-07-13
