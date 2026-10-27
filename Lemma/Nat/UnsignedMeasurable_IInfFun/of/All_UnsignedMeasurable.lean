import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open UnsignedMeasurable


/--
[UnsignedMeasurable.inf](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: ℕ → EuclideanSpace' d → EReal}
-- given
  (hf: ∀ n, UnsignedMeasurable (f n)) :
-- imply
  UnsignedMeasurable (fun x ↦ iInf (fun n ↦ f n x)) :=
-- proof
  UnsignedMeasurable.inf hf


-- created on 2026-10-22
