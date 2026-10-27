import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open UnsignedSimpleFunction


/--
[UnsignedSimpleFunction.unsigned](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf: UnsignedSimpleFunction f) :
-- imply
  Unsigned f :=
-- proof
  UnsignedSimpleFunction.unsigned hf


-- created on 2026-10-22
