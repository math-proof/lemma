import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_2
open Remark_1_3_10


/--
[exists_nonmeasurable_with_cantor_image](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_2.lean)
-/
@[path]
private lemma main
  :
-- imply
  ∃ F : Set ℝ, ∃ A : Set ℝ, F ⊆ Set.Icc 0 1 ∧
      ¬ LebesgueMeasurable (Real.equiv_EuclideanSpace' '' F) ∧
      binaryToTernary '' F ⊆ CantorSet ∧
      F ⊆ A ∧
      A ⊆ Set.Icc 0 1 ∧
      (Set.Icc 0 1 \ A).Countable ∧
      Set.InjOn binaryToTernary A :=
-- proof
  Remark_1_3_10.exists_nonmeasurable_with_cantor_image


-- created on 2026-10-22
