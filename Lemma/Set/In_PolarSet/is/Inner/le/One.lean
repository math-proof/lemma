import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.PolarSet

open InnerProductSpace.PolarSet.MetaMathlibExt


/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma mem_polar_set_iff
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : Set E} {y : E} :
-- imply
  y ∈ polarSet A ↔ ∀ x ∈ A, inner ℝ x y ≤ 1 := by
-- proof
  apply mem_polarSet

-- created on 2026-10-10
