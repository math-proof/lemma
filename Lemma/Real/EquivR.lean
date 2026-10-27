import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Section_5_epilogue.Part5
open Chapter5 hiding Real
open Chapter5.Real


/--
[Real.equivR_map_inv](https://github.com/teorth/analysis/blob/main/Analysis/Section_5_epilogue.lean)
-/
@[path]
private lemma main
  {x: Chapter5.Real} :
-- imply
  equivR (x⁻¹) = (equivR x)⁻¹ :=
-- proof
  Chapter5.Real.equivR_map_inv


-- created on 2026-10-22
