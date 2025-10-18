import sympy.functions.elementary.integers
import Lemma.Nat.NotGe.is.Lt
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Nat.EqSubAdd
import Lemma.Nat.LeSub_1
import Lemma.Nat.Eq.of.Le.Ge
import Lemma.Nat.LtSub_1.of.Ne_0
import Lemma.Nat.Ne.of.Lt
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n < 0) :
-- imply
  n ≥ n - 1 + 1 := by
-- proof
  by_contra h'
  have h' := Lt.of.NotGe h'
  have h' := Le_Sub_1.of.Lt h'
  rw [EqSubAdd] at h'
  have h' := Eq.of.Le.Ge h' (LeSub_1 n)
  have h := LtSub_1.of.Ne_0 (Ne.of.Lt h)
  rw [← h'] at h
  simp at h


-- created on 2025-08-13
