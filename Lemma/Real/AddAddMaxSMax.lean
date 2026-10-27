import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open Real


/--
[Real.pos_neg_add_identity](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {a b : ℝ} :
-- imply
  max (a + b) 0 + max (-a) 0 + max (-b) 0 =
    max a 0 + max b 0 + max (-(a + b)) 0 :=
-- proof
  Real.pos_neg_add_identity a b


-- created on 2026-10-22
