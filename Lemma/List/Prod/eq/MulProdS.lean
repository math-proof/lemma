import Lemma.Nat.Mul
open Nat


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.take i).prod * (s.drop i).prod := by
-- proof
  simp


@[main]
private lemma Comm
  [CommMonoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.drop i).prod * (s.take i).prod := by
-- proof
  rw [main s i]
  apply Mul.comm


-- created on 2025-06-08
