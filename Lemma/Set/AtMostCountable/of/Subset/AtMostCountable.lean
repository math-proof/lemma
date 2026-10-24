import Mathlib
import sympy.Basic
import sympy.analysis.Section_8_1
open Chapter8
open Chapter8.AtMostCountable


/--
[AtMostCountable.subset'](https://github.com/teorth/analysis/blob/main/Analysis/Section_8_1.lean)
-/
@[path]
private lemma main
  {X Y: Set A}
-- given
  (hX: AtMostCountable X)
  (hY: Y ⊆ X) :
-- imply
  AtMostCountable Y :=
-- proof
  Chapter8.AtMostCountable.subset' hX hY


-- created on 2026-10-22
