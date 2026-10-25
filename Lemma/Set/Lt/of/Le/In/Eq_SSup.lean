import Mathlib
import sympy.Basic
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part16
open BoundedInterval


/--
[lt_sSup_of_ne_sSup](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_1_1.lean)
-/
@[path]
private lemma main
  {X : Set ℝ}
  {x b : ℝ}
  {hBddAbove : BddAbove X}
-- given
  (hb : b = sSup X)
  (hb_notin : b ∉ X)
  (hx : x ∈ X)
  (hx_le_b : x ≤ b) :
-- imply
  x < b :=
-- proof
  lt_sSup_of_ne_sSup hBddAbove hb hb_notin hx hx_le_b


-- created on 2026-10-22
