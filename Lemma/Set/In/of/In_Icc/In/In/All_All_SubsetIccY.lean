import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[mem_of_mem_Icc_ordConnected](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {X : Set ℝ}
  {x w z : ℝ}
-- given
  (hOrdConn : ∀ ⦃x : ℝ⦄, x ∈ X → ∀ ⦃y : ℝ⦄, y ∈ X → Set.Icc x y ⊆ X)
  (hw : w ∈ X)
  (hz : z ∈ X)
  (hx : x ∈ Set.Icc w z) :
-- imply
  x ∈ X :=
-- proof
  mem_of_mem_Icc_ordConnected hOrdConn hw hz hx


-- created on 2026-10-22
