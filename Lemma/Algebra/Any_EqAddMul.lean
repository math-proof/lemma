import Lemma.Algebra.Eq_AddMulDiv___Mod
open Algebra


@[main]
private lemma main
-- given
  (m n : ℕ) :
-- imply
  ∃ i j, i * n + j = m := by
-- proof
  use m / n, m % n
  apply Eq.symm
  apply Eq_AddMulDiv___Mod


-- created on 2025-05-29
