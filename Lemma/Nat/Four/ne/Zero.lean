import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_1
import Lemma.Nat.Ne0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.four_ne](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  (4:Chapter2.Nat) ≠ 0 :=
-- proof
  by
    change 3++ ≠ 0
    exact Ne0


-- created on 2026-10-22
-- updated on 2026-10-23
