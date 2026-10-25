import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval


/--
[exercise_1_2_1_union](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∃ E: ℕ → Set ℝ, (∀ n, Bornology.IsBounded (E n)) ∧
        (∀ n, JordanMeasurable (Real.equiv_EuclideanSpace' '' (E n))) ∧
        (∀ n, E n ⊆ Set.Icc 0 1) ∧
        ¬ JordanMeasurable (⋃ n, Real.equiv_EuclideanSpace' '' (E n)) :=
-- proof
  exercise_1_2_1_union


-- created on 2026-10-22
