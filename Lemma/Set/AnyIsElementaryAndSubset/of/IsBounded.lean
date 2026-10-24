import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_2
open BoundedInterval
open Bornology
open Bornology.IsBounded


/--
[Bornology.IsBounded.inElementary](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_2.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  ∃ (A: Set (EuclideanSpace' d)), IsElementary A ∧ E ⊆ A :=
-- proof
  Bornology.IsBounded.inElementary hE


-- created on 2026-10-22
