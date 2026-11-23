module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.Analysis.Section_2_2.Part2
public import Theorem.Nat.IsPos.is.Ne_0
public import Theorem.Nat.IsPosAdd.of.IsPos
public import Theorem.Nat.Add.of.IsPos

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_eq_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
public theorem main
  {a b:Chapter2.Nat}
-- given
  (hab: a + b = 0) :
-- imply
  a = 0 ∧ b = 0 :=
-- proof
  by
    by_contra h
    simp only [not_and_or, ← ne_eq] at h
    obtain ha | hb := h
    ·
      rw [← IsPos.is.Ne_0] at ha
      observe : (a + b).IsPos
      contradiction
    rw [← IsPos.is.Ne_0] at hb
    observe : (a + b).IsPos
    contradiction


-- created on 2026-10-22
-- updated on 2026-10-26
