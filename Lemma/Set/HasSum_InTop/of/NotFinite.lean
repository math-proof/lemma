import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_0
open BoundedInterval
open Classical


/--
[hasSum_indicator_top_of_infinite](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {X : Set ℕ}
-- given
  (hX : ¬X.Finite) :
-- imply
  HasSum (fun n => if n ∈ X then (1 : EReal) else 0) ⊤ :=
-- proof
  hasSum_indicator_top_of_infinite X hX


-- created on 2026-10-22
