import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_8_3
open Chapter8
open Chapter8.EqualCard


/--
[EqualCard.power_set_false](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  ¬ EqualCard X (Set X) :=
-- proof
  Chapter8.EqualCard.power_set_false X


-- created on 2026-10-22
