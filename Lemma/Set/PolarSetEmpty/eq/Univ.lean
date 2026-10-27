import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.PolarSet

open InnerProductSpace.PolarSet.MetaMathlibExt


/--
[PolarSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/PolarSet.lean)
-/
@[path]
private lemma polar_set_empty_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
-- imply
  polarSet (∅ : Set E) = Set.univ := by
-- proof
  apply polarSet_empty

-- created on 2026-10-10
