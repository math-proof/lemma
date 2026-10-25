import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4


/--
[Jordan_inner_bddAbove](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  BddAbove { m:ℝ | ∃ (A: Set (EuclideanSpace' d)), ∃ hA: IsElementary A,
        A ⊆ E ∧ m = hA.measure } :=
-- proof
  Jordan_inner_bddAbove hE


-- created on 2026-10-22
