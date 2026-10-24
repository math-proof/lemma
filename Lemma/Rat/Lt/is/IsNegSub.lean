import Mathlib
import sympy.Basic
import sympy.analysis.Section_4_2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.lt_iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {x y:Section_4_2.Rat} :
-- imply
  x < y ↔ (x-y).isNeg :=
-- proof
  Section_4_2.Rat.lt_iff x y


-- created on 2026-10-22
