import Mathlib
import sympy.Basic
import Abbrev.Analysis.Section_11_3.Part5
open Chapter11.BoundedInterval Chapter9
open Chapter11
open Chapter11.MinorizesOn


/--
[MinorizesOn.iff](https://github.com/teorth/analysis/blob/main/Analysis/Section_11_3.lean)
-/
@[path]
private lemma main
  {g f:ℝ → ℝ}
  {I: BoundedInterval} :
-- imply
  MinorizesOn g f I ↔ MajorizesOn f g I :=
-- proof
  Chapter11.MinorizesOn.iff g f I


-- created on 2026-10-22
