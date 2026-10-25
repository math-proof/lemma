import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_3_2.Part9
open UnsignedMeasurable


/--
[UnsignedMeasurable.aeLimit](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
  {g: ℕ → EuclideanSpace' d → EReal}
-- given
  (hf: ∀ n, UnsignedMeasurable (g n))
  (hfn : Unsigned f)
  (heq: PointwiseAeConvergesTo g f) :
-- imply
  UnsignedMeasurable f :=
-- proof
  UnsignedMeasurable.aeLimit g hf hfn heq


-- created on 2026-10-22
