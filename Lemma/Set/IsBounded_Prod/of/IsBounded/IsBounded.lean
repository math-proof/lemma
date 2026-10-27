import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_isBounded](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {E₁ : Set (EuclideanSpace' d₁)}
  {E₂ : Set (EuclideanSpace' d₂)}
-- given
  (hE₁ : Bornology.IsBounded E₁)
  (hE₂ : Bornology.IsBounded E₂) :
-- imply
  Bornology.IsBounded (EuclideanSpace'.prod E₁ E₂) :=
-- proof
  EuclideanSpace'.prod_isBounded hE₁ hE₂


-- created on 2026-10-22
