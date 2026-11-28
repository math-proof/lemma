module

public import Theorem.Nat.Le.of.Lt
public import Theorem.Nat.EqMin.of.Le
public import Initialize.Tactic.Attr.Basic

public section

open Nat


@[path]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ⊓ b = a :=
-- proof
  EqMin.of.Le (Le.of.Lt h)


-- created on 2018-08-31
-- updated on 2025-10-12
