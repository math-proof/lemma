import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[f_lifted_le_one](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {x : EuclideanSpace' 1} :
-- imply
  f_lifted x ≤ 1 :=
-- proof
  Remark_1_3_10.f_lifted_le_one x


-- created on 2026-10-22
