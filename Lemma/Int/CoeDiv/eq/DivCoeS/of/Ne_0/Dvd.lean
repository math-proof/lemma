import Lemma.Int.NeCoe_0.is.Ne_0
open Int


@[main, comm]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {m n : ℤ}
-- given
  (n_dvd : n ∣ m)
  (hn : n ≠ 0) :
-- imply
  (m / n : ℤ) = (m / n : α) := by
-- proof
  apply Int.cast_div n_dvd
  apply NeCoe_0.of.Ne_0 hn


-- created on 2025-11-07
