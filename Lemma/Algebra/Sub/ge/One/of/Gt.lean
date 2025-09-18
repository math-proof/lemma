import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Algebra.Add
import Lemma.Algebra.LeAddS.is.Le
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.EqAddSub.of.Ge
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b > a) :
-- imply
  b - a ≥ 1 := by
-- proof
  have h_ge := LeAdd_1.of.Lt h
  rw [Add.comm] at h_ge
  have h_le := Le.of.Lt h
  have h_eq := EqAddSub.of.Ge h_le
  rw [← h_eq] at h_ge
  apply Le.of.LeAddS h_ge


-- created on 2025-06-21
