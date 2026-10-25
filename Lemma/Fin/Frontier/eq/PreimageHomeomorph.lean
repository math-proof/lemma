import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.frontier_toSet](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d} :
-- imply
  frontier B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      frontier (Set.univ.pi (fun i => (B.side i).toSet)) :=
-- proof
  Box.frontier_toSet B


-- created on 2026-10-22
