import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc_revealmuleone
open Finset StatMech StatMech.Walls


/--
[oc_reveal_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_revealmuleone.lean)
-/
@[path]
private lemma oc_reveal_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ reveal ν T e := by
-- proof
  apply StatMech.Walls.oc_reveal_nonneg hν T e

/--
[oc_reveal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_revealmuleone.lean)
-/
@[path]
private lemma oc_reveal_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  reveal ν T e ≤ 1 := by
-- proof
  apply StatMech.Walls.oc_reveal_le_one hν T e

/--
[oc_reveal_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_revealmuleone.lean)
-/
@[path]
private lemma oc_reveal_mem_Icc_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  reveal ν T e ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Walls.oc_reveal_mem_Icc hν T e

/--
[oc_revealmu_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_revealmuleone.lean)
-/
@[path]
private lemma oc_revealmu_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {T : DecisionTree E}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  0 ≤ reveal ν T e ∧ reveal ν T e ≤ 1 := by
-- proof
  apply StatMech.Walls.oc_revealmu_le_one hν T e


-- created on 2026-10-23
