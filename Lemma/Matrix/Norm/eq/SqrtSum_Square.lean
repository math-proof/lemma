import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open EuclideanSpace'


/--
[EuclideanSpace'.norm_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {n:ℕ}
  {x: EuclideanSpace' n} :
-- imply
  ‖x‖ = √(∑ i, (x i)^2) :=
-- proof
  EuclideanSpace'.norm_eq x


-- created on 2026-10-22
