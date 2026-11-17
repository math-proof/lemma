module

public import Mathlib
public import Abbrev.Analysis.Section_2_1
public import Theorem.Nat.Ne0

public section

open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.four_ne](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.Four.ne.Zero
  :
-- imply
  (4:Chapter2.Nat) ≠ 0 :=
-- proof
  by
    change 3++ ≠ 0
    exact Ne0


-- created on 2026-10-22
-- updated on 2026-10-26
