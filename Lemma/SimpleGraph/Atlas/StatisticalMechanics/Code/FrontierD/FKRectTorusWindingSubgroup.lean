import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup
open SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkRectClosedWindingSubgroup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean)
-/
@[path]
private lemma mem_fkRectClosedWindingSubgroup_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {u : Int × Int} :
-- imply
  u ∈ fkRectClosedWindingSubgroup R omega x ↔ ∃ p : (fkRectOpenGraph R omega).Walk x x, fkRectWalkWinding R p = u := by
-- proof
  apply StatMech.FrontierD.mem_fkRectClosedWindingSubgroup_iff R omega x u

/--
[fkRectClosedWindingSubgroup_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean)
-/
@[path]
private lemma fkRectClosedWindingSubgroup_eq_of_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectOpenGraph R omega).Reachable x y) :
-- imply
  fkRectClosedWindingSubgroup R omega x = fkRectClosedWindingSubgroup R omega y := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWindingSubgroup_eq_of_reachable R omega hxy

/--
[fkRectWindingSubgroupRankTwo_iff_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean)
-/
@[path]
private lemma fkRectWindingSubgroupRankTwo_iff_of_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectOpenGraph R omega).Reachable x y) :
-- imply
  FKRectWindingSubgroupRankTwo R omega x ↔ FKRectWindingSubgroupRankTwo R omega y := by
-- proof
  apply StatMech.FrontierD.fkRectWindingSubgroupRankTwo_iff_of_reachable R omega hxy

/--
[fkRectHasNet_iff_exists_windingSubgroup_rankTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean)
-/
@[path]
private lemma fkRectHasNet_iff_exists_windingSubgroup_rankTwo_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectHasNet R omega ↔ ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectHasNet_iff_exists_windingSubgroup_rankTwo R omega

/--
[fkRectNetIndicator_eq_one_iff_exists_windingSubgroup_rankTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingSubgroup.lean)
-/
@[path]
private lemma fkRectNetIndicator_eq_one_iff_exists_windingSubgroup_rankTwo_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectNetIndicator R omega = 1 ↔ ∃ x : R.Vertex, FKRectWindingSubgroupRankTwo R omega x := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_eq_one_iff_exists_windingSubgroup_rankTwo R omega


-- created on 2026-10-23
