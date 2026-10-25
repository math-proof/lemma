import Mathlib
import sympy.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.div_eq](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {q r:Section_4_2.Rat} :
-- imply
  q/r = q * r⁻¹ :=
-- proof
  Section_4_2.Rat.div_eq q r


-- created on 2026-10-22
