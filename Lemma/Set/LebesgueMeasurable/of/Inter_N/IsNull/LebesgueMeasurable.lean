import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open LebesgueMeasurable


/--
[LebesgueMeasurable.of_ae_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {A B N : Set (EuclideanSpace' d)}
-- given
  (hB : LebesgueMeasurable B)
  (hN : IsNull N)
  (h_eq : A ∩ Nᶜ = B ∩ Nᶜ) :
-- imply
  LebesgueMeasurable A :=
-- proof
  LebesgueMeasurable.of_ae_eq hB hN h_eq


-- created on 2026-10-22
