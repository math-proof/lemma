import Lemma.Algebra.EqMul0'0
import Lemma.Algebra.EqMul_0'0
open Algebra


@[main]
private lemma left
  [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b ≠ 0) :
-- imply
  a ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  rw [EqMul0'0] at h
  simp at h


@[main]
private lemma main
  [MulZeroClass α]
  {a b : α}
-- given
  (h : a * b ≠ 0) :
-- imply
  b ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h
  rw [EqMul_0'0] at h
  simp at h


-- created on 2025-04-12
