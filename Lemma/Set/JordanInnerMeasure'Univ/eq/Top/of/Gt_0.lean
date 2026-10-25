import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_inner_measure'_univ](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
-- given
  (hd: 0 < d) :
-- imply
  Jordan_inner_measure' (Set.univ : Set (EuclideanSpace' d)) = ⊤ :=
-- proof
  Jordan_inner_measure'_univ hd


-- created on 2026-10-22
