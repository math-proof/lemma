import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.Section_4_2.Part2
open Section_4_2 hiding Rat
open Section_4_2.Rat


/--
[Rat.intCast_neg](https://github.com/teorth/analysis/blob/main/Analysis/Section_4_2.lean)
-/
@[path]
private lemma main
  {a:ℤ} :
-- imply
  - (a:Section_4_2.Rat) = (-a:ℤ) :=
-- proof
  Section_4_2.Rat.intCast_neg a


-- created on 2026-10-22
