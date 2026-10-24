import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real
open Chapter5.BoundedAwayZero


/--
[BoundedAwayZero.const](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {q : ℚ}
-- given
  (hq : q ≠ 0) :
-- imply
  BoundedAwayZero fun _ ↦ q :=
-- proof
  Chapter5.BoundedAwayZero.const hq


-- created on 2026-10-22
