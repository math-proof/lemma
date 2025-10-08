import Lemma.Algebra.Mul2.eq.Add
open Algebra


@[main]
private lemma main
  {x : ℕ} :
-- imply
  2 * x - x = x := by
-- proof
  rw [Mul2.eq.Add]
  simp


-- created on 2025-10-08
