import Mathlib
import sympy.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.sub_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a b:Section_4_2.Rat} :
-- imply
  a - b = a + (-b) :=
-- proof
  Section_4_2.Rat.sub_eq a b


-- created on 2026-10-22
