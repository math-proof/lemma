import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[sqrt_sum_le_sum_sqrt](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  [Fintype ι] [DecidableEq ι]
  {f : ι → ℝ}
-- given
  (hf : ∀ i, 0 ≤ f i) :
-- imply
  √(∑ i, f i) ≤ ∑ i, √(f i) :=
-- proof
  Real.sqrt_sum_le_sum_sqrt f hf


-- created on 2026-10-20
