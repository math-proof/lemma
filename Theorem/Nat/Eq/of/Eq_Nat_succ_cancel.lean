module

public import Mathlib
public import Abbrev.Analysis.Section_2_1

public section

open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.succ_cancel](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
public theorem Nat.Eq.of.Eq_Nat_succ_cancel
  {n m:Chapter2.Nat}
-- given
  (hnm: n++ = m++) :
-- imply
  n = m :=
-- proof
  by
    injection hnm


-- created on 2026-10-22
-- updated on 2026-10-26
