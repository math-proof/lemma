import Mathlib
import sympy.Basic
import sympy.analysis.Misc.«Real-EReal-ENNReal»


/--
[tsum_coe_ennreal_eq_top_of_tsum_eq_top](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f : α → ENNReal}
-- given
  (h : ∑' i, f i = ⊤) :
-- imply
  ∑' i, (f i : EReal) = ⊤ :=
-- proof
  EReal.tsum_coe_ennreal_eq_top_of_tsum_eq_top h


-- created on 2026-10-20
