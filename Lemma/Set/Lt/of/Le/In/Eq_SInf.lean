import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[sInf_lt_of_ne_sInf](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {X : Set ℝ}
  {a x : ℝ}
  {hBddBelow : BddBelow X}
-- given
  (ha : a = sInf X)
  (ha_notin : a ∉ X)
  (hx : x ∈ X)
  (ha_le_x : a ≤ x) :
-- imply
  a < x :=
-- proof
  sInf_lt_of_ne_sInf hBddBelow ha ha_notin hx ha_le_x


-- created on 2026-10-22
