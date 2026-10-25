import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_5.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.LUB_claim1](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_5.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {E: Set Chapter5.Real}
-- given
  (hE: Set.Nonempty E)
  (hbound: BddAbove E) :
-- imply
  ∃! m:ℤ,
        (((m:ℚ) / (n+1):ℚ):Chapter5.Real) ∈ upperBounds E
        ∧ ¬ (((m:ℚ) / (n+1) - 1 / (n+1):ℚ):Chapter5.Real) ∈ upperBounds E :=
-- proof
  Chapter5.Real.LUB_claim1 n hE hbound


-- created on 2026-10-22
