import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Analysis.MeasureTheory.Section_1_1_2.Part4
open Pointwise
open EuclideanSpace'


/--
[EuclideanSpace'.prod_mono](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_2.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {E₁ E₁' : Set (EuclideanSpace' d₁)}
  {E₂ E₂' : Set (EuclideanSpace' d₂)}
-- given
  (h₀ : E₁ ⊆ E₁')
  (h₁ : E₂ ⊆ E₂') :
-- imply
  EuclideanSpace'.prod E₁ E₂ ⊆ EuclideanSpace'.prod E₁' E₂' :=
-- proof
  EuclideanSpace'.prod_mono h₀ h₁


-- created on 2026-10-22
