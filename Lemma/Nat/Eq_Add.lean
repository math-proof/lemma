import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
open Chapter2 hiding Nat
open Chapter2.Nat


/--
[Nat.succ_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {n m: Chapter2.Nat} :
-- imply
  n++ + m = (n+m)++ :=
-- proof
  rfl


-- created on 2026-10-22
-- updated on 2026-10-23
