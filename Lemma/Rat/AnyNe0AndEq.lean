import Mathlib
import sympy.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.eq_diff](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {n:Section_4_2.Rat} :
-- imply
  ∃ a b, b ≠ 0 ∧ n = a // b :=
-- proof
  Section_4_2.Rat.eq_diff n


-- created on 2026-10-22
