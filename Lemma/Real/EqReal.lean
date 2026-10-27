import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_3.Part12
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.inv_ratCast](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_3.lean)
-/
@[path]
private lemma main
  {q:ℚ} :
-- imply
  (q:Chapter5.Real)⁻¹ = (q⁻¹:ℚ) :=
-- proof
  Chapter5.Real.inv_ratCast q


-- created on 2026-10-22
