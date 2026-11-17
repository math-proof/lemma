module

public import Theorem.Nat.Le.of.Lt
public import Theorem.Nat.Sub.eq.Zero.of.Le

public section

open Nat


public theorem Nat.Sub.eq.Zero.of.Lt
-- given
  (h : a < b) :
-- imply
  a - b = 0 := by
-- proof
  have h := Le.of.Lt h
  apply Sub.eq.Zero.of.Le h


-- created on 2025-05-14
