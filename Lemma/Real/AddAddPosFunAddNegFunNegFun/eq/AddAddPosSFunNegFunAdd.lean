import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
open EReal


/--
[EReal.pos_neg_add_identity](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_4.lean)
-/
@[path]
private lemma main
  {f g : X → ℝ} :
-- imply
  EReal.pos_fun (f + g) + EReal.neg_fun f + EReal.neg_fun g =
    EReal.pos_fun f + EReal.pos_fun g + EReal.neg_fun (f + g) :=
-- proof
  EReal.pos_neg_add_identity f g


-- created on 2026-10-22
