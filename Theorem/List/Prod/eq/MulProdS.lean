module

public import Theorem.Nat.Mul
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[comm]
public theorem List.Prod.eq.MulProdS
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.take i).prod * (s.drop i).prod := by
-- proof
  simp


@[comm]
public theorem List.Prod.eq.MulProdS.comm
  [CommMonoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.prod = (s.drop i).prod * (s.take i).prod := by
-- proof
  rw [List.Prod.eq.MulProdS s i]
  apply Nat.Mul.Comm


-- created on 2025-06-08
