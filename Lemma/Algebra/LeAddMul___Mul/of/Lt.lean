import Lemma.Algebra.LeMulS.of.Le.Ge_0
import Lemma.Algebra.LeAdd_1.of.Lt
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  {m i : ℕ}
-- given
  (h : i < m)
  (n : ℕ) :
-- imply
  i * n + n ≤ m * n := by
-- proof
  have h := LeMulS.of.Le.Ge_0 (LeAdd_1.of.Lt h) (by simp : n >= 0)
  rw [MulAdd.eq.AddMulS] at h
  simp at h
  assumption


-- created on 2024-07-01
