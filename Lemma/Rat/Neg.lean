import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.Misc.SI.Part2
open Rat


/--
[Rat.neg_eq](https://github.com/teorth/analysis/blob/main/Analysis/Misc/SI.lean)
-/
@[path]
private lemma main
  {q:ℚ} :
-- imply
  Rat.neg q = -q :=
-- proof
  Rat.neg_eq q


-- created on 2026-10-22
