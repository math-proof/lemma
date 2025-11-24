import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.ModMod_Mul.eq.Mod
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {m n : Z}
-- given
  (h : n ∣ m)
  (k : Z) :
-- imply
  k % m % n = k % n := by
-- proof
  let ⟨d, h_m⟩ := Any_Eq_Mul.of.Dvd.left h
  subst h_m
  apply ModMod_Mul.eq.Mod


-- created on 2025-11-14
