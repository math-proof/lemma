import Lemma.Nat.EqMod.of.Lt
open Nat


@[main, comm]
private lemma main
  [NeZero n]
  {m : ℕ}
-- given
  (h : m > n) :
-- imply
  m - n % m = (m - n) % m := by
-- proof
  repeat rw [EqMod.of.Lt]
  ·
    have : n > 0 := NeZero.pos n
    omega
  ·
    assumption


-- created on 2025-10-19
