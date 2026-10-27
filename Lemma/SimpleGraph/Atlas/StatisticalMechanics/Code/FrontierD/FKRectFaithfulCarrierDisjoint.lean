import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
open SimpleGraph StatMech StatMech.FrontierD


/--
[FKRectIntegralSquareDartPath.ne_nil_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulCarrierDisjoint.lean)
-/
@[path]
private lemma ne_nil_of_ne_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l)
  (hpq : p ≠ q) :
-- imply
  l ≠ [] := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.ne_nil_of_ne h hpq

/--
[FKRectIntegralSquareDartPath.exists_faithfulShearWalk_of_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulCarrierDisjoint.lean)
-/
@[path]
private lemma exists_faithfulShearWalk_of_ne_nil_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l)
  (hl : l ≠ []) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q), ∀ z ∈ V.support, ∃ d ∈ l, ∃ r ∈ fkRectFaithfulShearDartRoute d, z = fkRectPairSite r := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.exists_faithfulShearWalk_of_ne_nil h hl

/--
[exists_fkRectFaithfulShearWalks_supportDisjoint_of_openBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulCarrierDisjoint.lean)
-/
@[path]
private lemma exists_fkRectFaithfulShearWalks_supportDisjoint_of_openBlocks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {F : Finset R.EdgeIndex}
  {p q a b : Int × Int}
  {l k : List FKRectIntegralSquareDart}
-- given
  (hF : ∀ e, e ∈ F ↔ omega e = true)
  (hlpath : FKRectIntegralSquareDartPath p q l)
  (hkpath : FKRectIntegralSquareDartPath a b k)
  (hlblocks : FKRectRefinedDualOpenEdgeBlocks R omega l)
  (hkblocks : FKRectRefinedOpenEdgeBlocks R F k)
  (hlne : l ≠ [])
  (hkne : k ≠ []) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint p) (fkRectFaithfulShearPoint q), ∃ W : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint a) (fkRectFaithfulShearPoint b), ∀ z, z ∈ V.support → z ∈ W.support → False := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFaithfulShearWalks_supportDisjoint_of_openBlocks R omega F hF hlpath hkpath hlblocks hkblocks hlne hkne


-- created on 2026-10-23
