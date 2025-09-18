import Lemma.Algebra.Eq_0.of.NotGt_0
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma left
  {k n m : ℕ}
-- given
  (h : n * m > k) :
-- imply
  n > 0 := by
-- proof
  by_contra h_n
  have h_n := Eq_0.of.NotGt_0 h_n
  rw [h_n] at h
  simp_all


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
