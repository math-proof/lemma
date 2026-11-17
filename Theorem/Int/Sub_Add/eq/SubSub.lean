module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Int.Sub_Add.eq.SubSub
  [SubtractionCommMonoid α]
-- given
  (a b c : α) :
-- imply
  a - (b + c) = a - b - c :=
-- proof
  sub_add_eq_sub_sub a b c



public theorem Int.SubSub.eq.Sub_Add
  [SubtractionCommMonoid α]
  (a b c : α) :
  a - b - c = a - (b + c) :=
  (Int.Sub_Add.eq.SubSub a b c).symm

-- created on 2024-07-01
-- updated on 2026-10-26
