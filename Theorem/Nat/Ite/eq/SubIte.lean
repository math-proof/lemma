module

public import Mathlib
public import Initialize.Tactic.Attr.Basic

public section


@[comm]
public theorem Nat.Ite.eq.SubIte
  [Decidable p]
  [Sub α]
  {a b c : α} :
-- imply
  (if p then
    a - c
  else
    b - c) = (if p then
    a
  else
    b) - c := by
-- proof
  split_ifs <;>
    rfl



public theorem Nat.SubIte.eq.Ite
  [Decidable p]
  [Sub α]
  {a b c : α} :
  (if p then a else b) - c =
    (if p then a - c else b - c) :=
  (Nat.Ite.eq.SubIte).symm

-- created on 2018-02-22
-- updated on 2026-10-26
