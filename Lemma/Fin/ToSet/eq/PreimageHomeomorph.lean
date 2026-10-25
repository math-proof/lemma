import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
open Box


/--
[Box.toSet_eq_ofLp_preimage](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_1.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {B : Box d} :
-- imply
  B.toSet = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹' Set.univ.pi (fun i => (B.side i).toSet) :=
-- proof
  Box.toSet_eq_ofLp_preimage B


-- created on 2026-10-22
