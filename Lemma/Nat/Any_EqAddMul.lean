import Lemma.Nat.EqAddMulDiv
open Nat


@[path]
private lemma main
  [IntegerRing Z]
-- given
  (m n : Z) :
-- imply
  ∃ i j, i * n + j = m := by
-- proof
  use m / n, m % n
  apply EqAddMulDiv


-- created on 2025-05-29
