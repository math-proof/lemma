import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.bddAbove_def](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {E: Set Chapter5.Real} :
-- imply
  BddAbove E ↔ ∃ M, M ∈ upperBounds E :=
-- proof
  Chapter5.Real.bddAbove_def E


-- created on 2026-10-22
