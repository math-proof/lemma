module

public import Mathlib
public import Abbrev.Analysis.Section_2_1
public import Theorem.Nat.Eq.of.Eq_Nat_succ_cancel
public import Theorem.Nat.Four.ne.Zero

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.six_ne_two](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.Six.ne.Two
  :
-- imply
  (6:Chapter2.Nat) ≠ 2 :=
-- proof
  by
    by_contra h
    change 5++ = 1++ at h
    apply Eq.of.Eq_Nat_succ_cancel at h
    change 4++ = 0++ at h
    apply Eq.of.Eq_Nat_succ_cancel at h
    have := Four.ne.Zero
    contradiction


-- created on 2026-10-22
-- updated on 2026-10-26
