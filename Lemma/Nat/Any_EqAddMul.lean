import Lemma.Nat.Eq_AddMulDiv___Mod
open Nat


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (m n : Z) :
-- imply
  ∃ i j, i * n + j = m := by
-- proof
  use m / n, m % n
  apply Eq.symm
  apply Eq_AddMulDiv___Mod


-- created on 2025-05-29
