import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
open BoundedInterval


/--
[Jordan_outer_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
-- given
  (hE: Bornology.IsBounded E) :
-- imply
  Jordan_outer_measure E = sInf (((fun S: Finset (Box d) ↦ ∑ B ∈ S, |B|ᵥ)) '' { S | E ⊆ ⋃ B ∈ S, B.toSet }) :=
-- proof
  Jordan_outer_eq hE


-- created on 2026-10-22
