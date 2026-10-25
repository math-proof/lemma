import Mathlib
import sympy.Basic
import Theorem.Analysis.Section_5_1.Part9
open Chapter5
open Chapter5.Sequence
open Chapter5.Sequence.IsCauchy


/--
[Sequence.IsCauchy.harmonic](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_1.lean)
-/
@[path]
private lemma main
  :
-- imply
  (mk' 1 (fun n ↦ (1:ℚ)/n)).IsCauchy :=
-- proof
  Chapter5.Sequence.IsCauchy.harmonic


-- created on 2026-10-22
