import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open JordanMeasurable


/--
[JordanMeasurable.mes_of_empty](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ} :
-- imply
  (JordanMeasurable.empty d).measure = 0 :=
-- proof
  JordanMeasurable.mes_of_empty d


-- created on 2026-10-22
