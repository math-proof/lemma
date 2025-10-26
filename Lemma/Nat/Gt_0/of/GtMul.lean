import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.Gt_0.of.Mul.gt.Zero
import Lemma.Nat.Mul
open Nat


@[main]
private lemma left
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  n > 0 :=
-- proof
  (Gt_0.of.Mul.gt.Zero.left ∘ Gt_0.of.Gt) h


@[main]
private lemma main
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  m > 0 := by
-- proof
  rw [Mul.comm] at h
  apply left h


-- created on 2025-05-29
-- updated on 2025-07-08
