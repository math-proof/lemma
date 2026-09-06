import Lemma.Nat.Any_Eq_Mul.of.Dvd
open Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n % d = 0) :
-- imply
  ∃ k, n = k * d :=
-- proof
  Any_Eq_Mul.of.Dvd.left (Int.dvd_of_emod_eq_zero h)


-- created on 2026-09-06
