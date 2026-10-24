import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.le_of_lt](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n m:Chapter2.Nat}
-- given
  (hnm: n < m) :
-- imply
  n ≤ m :=
-- proof
  hnm.1


-- created on 2026-10-22
-- updated on 2026-10-23
