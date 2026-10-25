import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_2_1
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.succ_cancel](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat}
-- given
  (hnm: n++ = m++) :
-- imply
  n = m :=
-- proof
  by
    injection hnm


-- created on 2026-10-22
-- updated on 2026-10-23
