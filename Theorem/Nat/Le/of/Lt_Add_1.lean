module

public import Initialize.Tactic.Attr.Basic

public import Theorem.Nat.LeAdd_1.of.Lt
public import Theorem.Nat.NotLe.is.Gt
public import Theorem.Nat.LtAddS.is.Lt
public import Theorem.Nat.Gt.of.Gt.Ge
public import Theorem.Nat.NotGt

public section

open Nat


@[comm 1]
public theorem Nat.Le.of.Lt_Add_1
  [IntegerRing Z]
  {x y : Z}
-- given
  (h : x < y + 1) :
-- imply
  x ≤ y := by
-- proof
  have h_Le := LeAdd_1.of.Lt h
  by_contra h'
  have := Gt.of.NotLe h'
  have : x + 1 > y + 1 := GtAddS.of.Gt this (a := 1)
  have := Gt.of.Gt.Ge this h_Le
  have := NotGt (a := x + 1)
  contradiction


-- created on 2025-03-29
