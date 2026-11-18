module

public import Mathlib
public import Abbrev.Analysis.Section_2_1
public import Theorem.Nat.Six.ne.Two

public section

open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.six_ne_two'](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.Ne62
  :
-- imply
  (6:Chapter2.Nat) ≠ 2 :=
-- proof
  Nat.Six.ne.Two


-- created on 2026-10-22
-- updated on 2026-10-26
