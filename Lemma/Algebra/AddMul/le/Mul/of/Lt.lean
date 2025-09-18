import Lemma.Algebra.AddMul.eq.Mul_Add_1
import Lemma.Algebra.LeMulS.of.Ge_0.Le
open Algebra


@[main]
private lemma main
  {i n : ℕ}
-- given
  (h : i < n) 
  (m : ℕ):
-- imply
  m * i + m ≤ m * n := by
-- proof
  rw [AddMul.eq.Mul_Add_1]
  apply LeMulS.of.Ge_0.Le (by simp) (by linarith)


-- created on 2025-05-31
