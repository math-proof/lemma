import Mathlib
import sympy.Basic
import sympy.analysis.Section_2_2
import Lemma.Nat.EqRecurseNat0
open Chapter2 hiding Nat
open Chapter2.Nat
open Nat


/--
[Nat.zero_add](https://github.com/teorth/analysis/blob/main/Analysis/Section_2_2.lean)
-/
@[path]
private lemma main
  {m: Chapter2.Nat} :
-- imply
  0 + m = m :=
-- proof
  EqRecurseNat0 (f := fun _ sum ↦ sum++)


-- created on 2026-10-22
-- updated on 2026-10-23
