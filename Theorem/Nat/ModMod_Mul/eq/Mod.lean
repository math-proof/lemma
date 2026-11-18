module

public import Theorem.Nat.Mul
public import Instance.Data.Int.Integers

public section

open Nat


public theorem Nat.ModMod_Mul.eq.Mod
  [IntegerRing Z]
-- given
  (k m n : Z) :
-- imply
  k % (m * n) % n = k % n :=
-- proof
  IntegerRing.mod_mul


public theorem Nat.ModMod_Mul.eq.Mod.left
  [IntegerRing Z]
-- given
  (k m n : Z) :
-- imply
  k % (n * m) % n = k % n := by
-- proof
  rw [Nat.Mul.Comm]
  apply Nat.ModMod_Mul.eq.Mod


-- created on 2025-11-14
-- updated on 2026-08-01
