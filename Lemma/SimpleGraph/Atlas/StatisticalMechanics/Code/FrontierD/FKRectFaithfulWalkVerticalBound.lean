import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
open SimpleGraph StatMech StatMech.FrontierD


/--
[exists_fkRectFaithfulWalk_vertical_natAbs_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulWalkVerticalBound.lean)
-/
@[path]
private lemma exists_fkRectFaithfulWalk_vertical_natAbs_bound_eq
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y} :
-- imply
  ∃ M : Nat, ∀ z ∈ W.support, -(M : Int) <= z 1 ∧ z 1 <= (M : Int) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFaithfulWalk_vertical_natAbs_bound W


-- created on 2026-10-23
