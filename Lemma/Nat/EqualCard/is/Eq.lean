import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.EqualCard


/--
[EqualCard.iff'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X Y : Type}
  :
-- imply
  EqualCard X Y ↔ Cardinal.mk X = Cardinal.mk Y :=
-- proof
  Chapter8.EqualCard.iff'


-- created on 2026-10-22
