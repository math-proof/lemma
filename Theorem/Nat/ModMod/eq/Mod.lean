module

public import Theorem.Nat.ModMod_Mul.eq.Mod

public section

open Nat


public theorem Nat.ModMod.eq.Mod
  [IntegerRing Z]
-- given
  (n d : Z) :
-- imply
  n % d % d = n % d := by
-- proof
  have := ModMod_Mul.eq.Mod n 1 d
  simp_all


-- created on 2025-06-16
-- updated on 2025-11-14
