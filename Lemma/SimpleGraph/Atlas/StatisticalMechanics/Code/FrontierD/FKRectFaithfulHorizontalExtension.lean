import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFaithfulHorizontalExtension_mem_support_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulHorizontalExtension.lean)
-/
@[path]
private lemma fkRectFaithfulHorizontalExtension_mem_support_iff_eq
  {alpha beta : Int}
  {x y z : Site 2}
  {W : (hypercubicLattice 2).Walk x y} :
-- imply
  z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support ↔ z ∈ (sw_horizSeg (x 1) alpha (x 0)).support ∨ z ∈ W.support ∨ z ∈ (sw_horizSeg (y 1) (y 0) beta).support := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulHorizontalExtension_mem_support_iff alpha beta W

/--
[fkRectFaithfulHorizontalExtension_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulHorizontalExtension.lean)
-/
@[path]
private lemma fkRectFaithfulHorizontalExtension_fst_bounds_eq
  {alpha beta : Int}
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
-- given
  (hx : alpha <= x 0)
  (hy : y 0 <= beta)
  (hW : ∀ z ∈ W.support, alpha <= z 0 ∧ z 0 <= beta) :
-- imply
  ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support, alpha <= z 0 ∧ z 0 <= beta := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulHorizontalExtension_fst_bounds alpha beta W hx hy hW

/--
[fkRectFaithfulHorizontalExtension_snd_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulHorizontalExtension.lean)
-/
@[path]
private lemma fkRectFaithfulHorizontalExtension_snd_bounds_eq
  {alpha beta lower upper : Int}
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
-- given
  (hW : ∀ z ∈ W.support, lower <= z 1 ∧ z 1 <= upper) :
-- imply
  ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support, lower <= z 1 ∧ z 1 <= upper := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulHorizontalExtension_snd_bounds alpha beta lower upper W hW

/--
[fkRectFaithfulHorizontalExtension_support_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulHorizontalExtension.lean)
-/
@[path]
private lemma fkRectFaithfulHorizontalExtension_support_rect_eq
  {alpha beta lower upper : Int}
  {x y : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
-- given
  (hx : alpha <= x 0)
  (hy : y 0 <= beta)
  (hW : ∀ z ∈ W.support, z ∈ rect alpha beta lower upper) :
-- imply
  ∀ z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support, z ∈ rect alpha beta lower upper := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulHorizontalExtension_support_rect alpha beta lower upper W hx hy hW

/--
[fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulHorizontalExtension.lean)
-/
@[path]
private lemma fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds_eq
  {alpha beta coreLeft coreRight : Int}
  {x y a b : Site 2}
  {W : (hypercubicLattice 2).Walk x y}
  {V : (hypercubicLattice 2).Walk a b}
-- given
  (hleft : alpha <= x 0)
  (hxcore : x 0 <= coreLeft)
  (hcorey : coreRight <= y 0)
  (hyright : y 0 <= beta)
  (hV : ∀ z ∈ V.support, coreLeft <= z 0 ∧ z 0 <= coreRight)
  (hdisjoint : ∀ z, z ∈ W.support -> z ∈ V.support -> False) :
-- imply
  ∀ z, z ∈ (fkRectFaithfulHorizontalExtension alpha beta W).support -> z ∈ V.support -> False := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulHorizontalExtension_support_disjoint_of_core_bounds alpha beta coreLeft coreRight W V hleft hxcore hcorey hyright hV hdisjoint


-- created on 2026-10-23
