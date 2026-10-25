import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open Box


/--
[Box.prod_pairwiseDisjoint](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d₁ d₂:ℕ}
  {S : Finset (Box d₁)}
  {T : Finset (Box d₂)}
-- given
  (hS : (S : Set (Box d₁)).PairwiseDisjoint Box.toSet)
  (hT : (T : Set (Box d₂)).PairwiseDisjoint Box.toSet) :
-- imply
  (((S ×ˢ T).image (fun p => p.1.prod p.2) : Finset (Box (d₁ + d₂))) :
      Set (Box (d₁ + d₂))).PairwiseDisjoint Box.toSet :=
-- proof
  Box.prod_pairwiseDisjoint hS hT


-- created on 2026-10-22
