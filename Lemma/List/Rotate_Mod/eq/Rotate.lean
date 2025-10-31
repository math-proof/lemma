import Lemma.Nat.ModMod.eq.Mod
open Nat


@[main]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  s.rotate (n % s.length) = s.rotate n:= by
-- proof
  unfold List.rotate
  rw [ModMod.eq.Mod]


-- created on 2025-06-16
