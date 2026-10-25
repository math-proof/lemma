import Mathlib
import sympy.Basic
import Abbrev.Analysis.Appendix_B_2
open NNReal AppendixB.NNRealDecimal
open AppendixB


/--
[NNRealDecimal.not_inj](https://github.com/teorth/analysis/blob/main/Analysis/Appendix_B_2.lean)
-/
@[path]
private lemma main
  :
-- imply
  (1:NNReal) = (mk 1 fun _ ↦ 0) ∧ (1:NNReal) = (mk 0 fun _ ↦ 9) :=
-- proof
  AppendixB.NNRealDecimal.not_inj


-- created on 2026-10-22
