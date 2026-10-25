import Mathlib
import sympy.Basic
import Theorem.Analysis.Misc.RealERealENNReal
open EReal


/--
[EReal.lt_add_of_pos_coe](https://github.com/teorth/analysis/blob/main/Analysis/Misc/Real-EReal-ENNReal.lean)
-/
@[path]
private lemma main
  {x : EReal}
  {ε : ℝ}
-- given
  (hε : 0 < ε)
  (h_ne_bot : x ≠ ⊥)
  (h_ne_top : x ≠ ⊤) :
-- imply
  x < x + ↑ε :=
-- proof
  EReal.lt_add_of_pos_coe hε h_ne_bot h_ne_top


-- created on 2026-10-22
