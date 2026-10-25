import Mathlib
import sympy.Basic
import Def.Analysis.MeasureTheory.Notation.Part2
open EuclideanSpace'


/--
[EuclideanSpace'.coord_le_norm](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Notation.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {x : EuclideanSpace' d}
  {i : Fin d} :
-- imply
  |x i| ≤ ‖x‖ :=
-- proof
  EuclideanSpace'.coord_le_norm x i


-- created on 2026-10-22
