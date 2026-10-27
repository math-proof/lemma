import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Section_6_2.Part2
open EReal


/--
[EReal.sup_of_neg_infty_mem](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_2.lean)
-/
@[path]
private lemma main
  {E: Set EReal} :
-- imply
  sSup E = sSup (E \ {⊥}) :=
-- proof
  EReal.sup_of_neg_infty_mem


-- created on 2026-10-22
