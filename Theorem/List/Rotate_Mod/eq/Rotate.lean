module

public import Theorem.Nat.ModMod.eq.Mod

public section

open Nat


public theorem List.Rotate_Mod.eq.Rotate
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  s.rotate (n % s.length) = s.rotate n:= by
-- proof
  unfold List.rotate
  rw [ModMod.eq.Mod]


-- created on 2025-06-16
