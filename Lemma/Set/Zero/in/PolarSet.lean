import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.PolarSet

open InnerProductSpace.PolarSet.MetaMathlibExt


/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma zero_mem_polar_set_is
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (A : Set E) :
-- imply
  (0 : E) ∈ polarSet A := by
-- proof
  apply zero_mem_polarSet A

-- created on 2026-10-10
