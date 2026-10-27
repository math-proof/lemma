import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.PolarSet

open InnerProductSpace.PolarSet.MetaMathlibExt


/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma polar_set_subset_polar_set_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A B : Set E}
  (h : A ⊆ B) :
-- imply
  polarSet B ⊆ polarSet A := by
-- proof
  apply polarSet_subset_polarSet h

-- created on 2026-10-10
