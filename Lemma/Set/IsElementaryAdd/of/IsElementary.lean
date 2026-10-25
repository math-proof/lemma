import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval
open Pointwise
open IsElementary


/--
[IsElementary.translate](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {E: Set (EuclideanSpace' d)}
  {x: EuclideanSpace' d}
-- given
  (hE: IsElementary E) :
-- imply
  IsElementary (E + {x}) :=
-- proof
  IsElementary.translate hE x


-- created on 2026-10-22
