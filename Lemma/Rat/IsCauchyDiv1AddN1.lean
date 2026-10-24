import Mathlib
import sympy.Basic
import sympy.analysis.Section_5_3
open Chapter5 hiding Real
open Chapter5.Sequence
open Chapter5.Sequence.IsCauchy


/--
[Sequence.IsCauchy.harmonic'](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  :
-- imply
  ((fun n ↦ 1/((n:ℚ)+1): ℕ → ℚ):Sequence).IsCauchy :=
-- proof
  Chapter5.Sequence.IsCauchy.harmonic'


-- created on 2026-10-22
