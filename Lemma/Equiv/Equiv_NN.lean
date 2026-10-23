import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_2
open Chapter5
open Chapter5.Sequence


/--
[Sequence.equiv_example](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_2.lean)
-/
@[path]
private lemma main
  :
-- imply
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) :=
-- proof
  Chapter5.Sequence.equiv_example


-- created on 2026-10-22
