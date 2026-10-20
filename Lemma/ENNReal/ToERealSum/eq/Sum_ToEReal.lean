import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[coe_ennreal_finset_sum](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {s : Finset α}
  {f : α → ENNReal} :
-- imply
  (∑ a ∈ s, f a : ENNReal).toEReal = ∑ a ∈ s, (f a).toEReal :=
-- proof
  EReal.coe_ennreal_finset_sum


-- created on 2026-10-20
