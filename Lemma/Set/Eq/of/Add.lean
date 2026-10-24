import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_1_1
open BoundedInterval
open Pointwise
open Set


/--
[Set.translate_inj](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {x: EuclideanSpace' d}
  {S₁ S₂ : Set (EuclideanSpace' d)}
-- given
  (h_eq : S₁ + {x} = S₂ + {x}) :
-- imply
  S₁ = S₂ :=
-- proof
  Set.translate_inj x S₁ S₂ h_eq


-- created on 2026-10-22
