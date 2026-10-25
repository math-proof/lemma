import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[coe_finset_sum](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {s : Finset α}
  {f : α → ℝ}
-- given
  (hf : ∀ a ∈ s, 0 ≤ f a) :
-- imply
  (∑ a ∈ s, f a).toEReal = ∑ a ∈ s, (f a).toEReal :=
-- proof
  EReal.coe_finset_sum hf


-- created on 2026-10-20
