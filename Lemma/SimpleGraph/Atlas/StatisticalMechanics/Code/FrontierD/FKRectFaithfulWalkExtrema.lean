import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkExtrema
open SimpleGraph StatMech StatMech.FrontierD


/--
[exists_fkRectFaithfulWalk_verticalExtremaSubwalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulWalkExtrema.lean)
-/
@[path]
private lemma exists_fkRectFaithfulWalk_verticalExtremaSubwalk_eq
  {x y : Site 2}
  {V : (hypercubicLattice 2).Walk x y} :
-- imply
  ∃ (lower upper : Int) (bottom top : Site 2), ∃ W : (hypercubicLattice 2).Walk bottom top, bottom 1 = lower ∧ top 1 = upper ∧ (∀ z ∈ V.support, lower ≤ z 1 ∧ z 1 ≤ upper) ∧ (∀ z ∈ W.support, z ∈ V.support) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFaithfulWalk_verticalExtremaSubwalk V


-- created on 2026-10-23
