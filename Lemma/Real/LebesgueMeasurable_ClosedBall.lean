import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open LebesgueMeasurable


/--
[LebesgueMeasurable.closedBall](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {c : EuclideanSpace' d}
  {r : ℝ} :
-- imply
  LebesgueMeasurable (Metric.closedBall c r) :=
-- proof
  LebesgueMeasurable.closedBall c r


-- created on 2026-10-22
