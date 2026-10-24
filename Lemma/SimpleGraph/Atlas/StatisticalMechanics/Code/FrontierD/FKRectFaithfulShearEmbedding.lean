import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearEmbedding
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectPairSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma fkRectPairSite_injective_eq :
-- imply
  Function.Injective fkRectPairSite := by
-- proof
  apply StatMech.FrontierD.fkRectPairSite_injective

/--
[fkRectFaithfulShearPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma fkRectFaithfulShearPair_injective_eq :
-- imply
  Function.Injective fkRectFaithfulShearPair := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPair_injective

/--
[fkRectFaithfulShearPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_injective_eq :
-- imply
  Function.Injective fkRectFaithfulShearPoint := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_injective

/--
[fkRectIntegralSquareDartsIncident_of_mem_faithfulRoutes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartsIncident_of_mem_faithfulRoutes_eq
  {d e : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hr : r ∈ fkRectFaithfulShearDartRoute d)
  (he : r ∈ fkRectFaithfulShearDartRoute e) :
-- imply
  FKRectIntegralSquareDartsIncident d e := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartsIncident_of_mem_faithfulRoutes d e r hr he

/--
[fkRectIntegralSquareDartsIncident_of_faithfulRouteSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartsIncident_of_faithfulRouteSite_eq
  {d e : FKRectIntegralSquareDart}
  {r s : Int × Int}
-- given
  (hr : r ∈ fkRectFaithfulShearDartRoute d)
  (hs : s ∈ fkRectFaithfulShearDartRoute e)
  (hsite : fkRectPairSite r = fkRectPairSite s) :
-- imply
  FKRectIntegralSquareDartsIncident d e := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartsIncident_of_faithfulRouteSite d e r s hr hs hsite

/--
[exists_fkRectFaithfulShearDartWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma exists_fkRectFaithfulShearDartWalk_eq
  {d : FKRectIntegralSquareDart} :
-- imply
  ∃ W : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint d.1) (fkRectFaithfulShearPoint (fkRectIntegralSquareDartEnd d)), ∀ z ∈ W.support, ∃ r ∈ fkRectFaithfulShearDartRoute d, z = fkRectPairSite r := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFaithfulShearDartWalk d

/--
[FKRectIntegralSquareDartPath.exists_faithfulShearWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearEmbedding.lean)
-/
@[path]
private lemma exists_faithfulShearWalk_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q), ∀ z ∈ V.support, z = fkRectFaithfulShearPoint p ∨ ∃ d ∈ l, ∃ r ∈ fkRectFaithfulShearDartRoute d, z = fkRectPairSite r := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.exists_faithfulShearWalk h


-- created on 2026-10-23
