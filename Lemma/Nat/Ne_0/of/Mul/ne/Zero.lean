import Lemma.Nat.EqMul0_0
import Lemma.Nat.EqMul_0'0
open Nat


@[path]
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
  rw [EqMul0_0] at h
  simp at h


@[path]
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
