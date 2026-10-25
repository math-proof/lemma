import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal


/--
[coe_ennreal](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {f : α → ENNReal} :
-- imply
  Summable (fun x => ↑(f x) : α → EReal) :=
-- proof
  Summable.coe_ennreal


-- created on 2026-10-20
