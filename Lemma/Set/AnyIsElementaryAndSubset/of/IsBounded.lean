import Mathlib
import sympy.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
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
