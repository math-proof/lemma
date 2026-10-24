import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.IsPos.is.Ne_0
import Lemma.Nat.IsPosAdd.of.IsPos
import Lemma.Nat.Add.of.IsPos
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.add_eq_zero](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
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
-- updated on 2026-10-23
