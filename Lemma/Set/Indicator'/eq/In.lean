import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open Set


/--
[Set.indicator'_apply](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {E: Set X}
  {x: X} [Decidable (x ∈ E)] :
-- imply
  indicator' E x = if x ∈ E then 1 else 0 :=
-- proof
  Set.indicator'_apply E x


-- created on 2026-10-22
