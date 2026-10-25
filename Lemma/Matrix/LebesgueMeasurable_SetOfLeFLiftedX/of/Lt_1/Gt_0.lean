import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open Remark_1_3_10


/--
[sublevel_set_measurable](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {t : EReal}
-- given
  (ht_pos : 0 < t)
  (ht_lt_one : t < 1) :
-- imply
  LebesgueMeasurable {x : EuclideanSpace' 1 | f_lifted x ≤ t} :=
-- proof
  Remark_1_3_10.sublevel_set_measurable t ht_pos ht_lt_one


-- created on 2026-10-22
