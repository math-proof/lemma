import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open IsOpen


/--
[IsOpen.exists_dyadic_cube_subset](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E : Set (EuclideanSpace' d)}
  {x : EuclideanSpace' d}
-- given
  (hE : IsOpen E)
  (hx : x ∈ E) :
-- imply
  ∃ n : ℕ, ∃ a : Fin d → ℤ, x ∈ (DyadicCube (n:ℤ) a).toSet ∧
      (DyadicCube (n:ℤ) a).toSet ⊆ E :=
-- proof
  IsOpen.exists_dyadic_cube_subset hE hx


-- created on 2026-10-22
