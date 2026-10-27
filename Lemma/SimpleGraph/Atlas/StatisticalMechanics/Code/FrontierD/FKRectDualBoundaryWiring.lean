import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBoundaryWiring
open SimpleGraph StatMech StatMech.FrontierD


/--
[finitePeriodicSucc_fkRectRightColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma finitePeriodicSucc_fkRectRightColumn_eq
  {R : FKRectTorus} :
-- imply
  finitePeriodicSucc R.width_pos (fkRectRightColumn R) = fkRectLeftColumn R := by
-- proof
  apply StatMech.FrontierD.finitePeriodicSucc_fkRectRightColumn R

/--
[fkRect_cyclicPred_eq_of_val_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRect_cyclicPred_eq_of_val_succ_eq
  {N : Nat}
  {u v : Fin N}
-- given
  (hN : 0 < N)
  (huv : u.val + 1 = v.val) :
-- imply
  SixVertexArrows.cyclicPred hN v = u := by
-- proof
  apply StatMech.FrontierD.fkRect_cyclicPred_eq_of_val_succ hN huv

/--
[fkRectDualOpenGraph_adj_right_of_val_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectDualOpenGraph_adj_right_of_val_succ_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {u v : Fin R.height}
-- given
  (hclosed : FKRectCutClosedConfiguration R eta)
  (huv : u.val + 1 = v.val) :
-- imply
  (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta)).Adj (fkRectRightColumn R, u) (fkRectRightColumn R, v) := by
-- proof
  apply StatMech.FrontierD.fkRectDualOpenGraph_adj_right_of_val_succ R eta hclosed huv

/--
[fkRectDualOpenGraph_rightBoundary_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectDualOpenGraph_rightBoundary_reachable_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {u v : Fin R.height}
-- given
  (hclosed : FKRectCutClosedConfiguration R eta) :
-- imply
  (fkRectOpenGraph R (fkRectDualConfigurationEquiv R eta)).Reachable (fkRectRightColumn R, u) (fkRectRightColumn R, v) := by
-- proof
  apply StatMech.FrontierD.fkRectDualOpenGraph_rightBoundary_reachable R eta hclosed u v

/--
[fkRectRawHorizontalCrossingClusterCount_dual_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingClusterCount_dual_le_one_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
-- given
  (hclosed : FKRectCutClosedConfiguration R eta) :
-- imply
  fkRectRawHorizontalCrossingClusterCount R (fkRectDualConfigurationEquiv R eta) ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingClusterCount_dual_le_one R eta hclosed

/--
[fkRectRawPrimalDualHorizontalCrossingClusterCount_le_primal_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectRawPrimalDualHorizontalCrossingClusterCount_le_primal_add_one_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
-- given
  (hclosed : FKRectCutClosedConfiguration R eta) :
-- imply
  fkRectRawPrimalDualHorizontalCrossingClusterCount R eta ≤ fkRectRawHorizontalCrossingClusterCount R eta + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalDualHorizontalCrossingClusterCount_le_primal_add_one R eta hclosed

/--
[fkRectCriticalCutFreeEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectCriticalCutFreeEventMass_mono_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hAB : A ⊆ B) :
-- imply
  fkRectCriticalCutFreeEventMass R q A ≤ fkRectCriticalCutFreeEventMass R q B := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFreeEventMass_mono R hq hAB

/--
[fkRectCriticalCutFreeEventMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectCriticalCutFreeEventMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 ≤ fkRectCriticalCutFreeEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFreeEventMass_nonneg R hq A

/--
[fkRectCriticalClosedMass_cut_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectCriticalClosedMass_cut_le_one_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalClosedMass_cut_le_one R hq

/--
[fkRectCriticalCutFree_primalDualCrossingTail_le_primalTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_primalDualCrossingTail_le_primalTail_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | n + 1 < fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} ≤ fkRectCriticalCutFreeEventMass R q {eta | n < fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_primalDualCrossingTail_le_primalTail R hq n

/--
[fkRectCriticalCutFree_primalDualCrossingTail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBoundaryWiring.lean)
-/
@[path]
private lemma fkRectCriticalCutFree_primalDualCrossingTail_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalCutFreeEventMass R q {eta | n + 1 < fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R eta)} ≤ Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFree_primalDualCrossingTail_le_choose_mul_pow R hq n


-- created on 2026-10-23
