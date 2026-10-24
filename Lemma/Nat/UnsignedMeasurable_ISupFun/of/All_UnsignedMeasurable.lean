import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open UnsignedMeasurable


/--
[UnsignedMeasurable.sup](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: ℕ → EuclideanSpace' d → EReal}
-- given
  (hf: ∀ n, UnsignedMeasurable (f n)) :
-- imply
  UnsignedMeasurable (fun x ↦ iSup (fun n ↦ f n x)) :=
-- proof
  UnsignedMeasurable.sup hf


-- created on 2026-10-22
