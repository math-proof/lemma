import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice
open Finset StatMech StatMech.FrontierD


/--
[mem_fkRectDualCutEdges_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma mem_fkRectDualCutEdges_iff_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  e ∈ fkRectDualCutEdges R ↔ fkRectDualEdgeToEdge R e ∈ fkRectTorusCutEdges R := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDualCutEdges_iff R e

/--
[fkRectWiredDualAddedEdges_disjoint_openEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectWiredDualAddedEdges_disjoint_openEdges_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Disjoint (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega)) (fkRectWiredDualAddedEdges R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectWiredDualAddedEdges_disjoint_openEdges R omega

/--
[fkRectDualConfiguration_forceCutClosed_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectDualConfiguration_forceCutClosed_apply_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) e = if e ∈ fkRectDualCutEdges R then true else fkRectDualConfigurationEquiv R omega e := by
-- proof
  apply StatMech.FrontierD.fkRectDualConfiguration_forceCutClosed_apply R omega e

/--
[fkRectOpenEdges_dual_forceCutClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectOpenEdges_dual_forceCutClosed_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdges R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) = fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪ fkRectDualCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdges_dual_forceCutClosed R omega

/--
[fkRectOpenEdges_dual_forceCutClosed_eq_inserted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectOpenEdges_dual_forceCutClosed_eq_inserted_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdges R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega)) = fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪ fkRectWiredDualAddedEdges R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdges_dual_forceCutClosed_eq_inserted R omega

/--
[fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) = fkRectConfigurationOfEdges R (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪ fkRectWiredDualAddedEdges R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectDual_forceCutClosed_eq_configurationOfInsertedEdges R omega

/--
[fkRectInsertEdgeList_eq_union_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectInsertEdgeList_eq_union_toFinset_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {es : List R.EdgeIndex} :
-- imply
  fkRectInsertEdgeList R F es = F ∪ es.toFinset := by
-- proof
  apply StatMech.FrontierD.fkRectInsertEdgeList_eq_union_toFinset R F es

/--
[fkRectWiredDualAddedEdgeList_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectWiredDualAddedEdgeList_toFinset_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (fkRectWiredDualAddedEdgeList R omega).toFinset = fkRectWiredDualAddedEdges R omega := by
-- proof
  apply StatMech.FrontierD.fkRectWiredDualAddedEdgeList_toFinset R omega

/--
[fkRectInsert_wiredDualAddedEdgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectInsert_wiredDualAddedEdgeList_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectInsertEdgeList R (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega)) (fkRectWiredDualAddedEdgeList R omega) = fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega) ∪ fkRectWiredDualAddedEdges R omega := by
-- proof
  apply StatMech.FrontierD.fkRectInsert_wiredDualAddedEdgeList R omega

/--
[fkRectDual_forceCutClosed_eq_configurationOfInsertedEdgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectDual_forceCutClosed_eq_configurationOfInsertedEdgeList_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectDualConfigurationEquiv R (fkRectForceCutClosed R omega) = fkRectConfigurationOfEdges R (fkRectInsertEdgeList R (fkRectOpenEdges R (fkRectDualConfigurationEquiv R omega)) (fkRectWiredDualAddedEdgeList R omega)) := by
-- proof
  apply StatMech.FrontierD.fkRectDual_forceCutClosed_eq_configurationOfInsertedEdgeList R omega

/--
[fkRectDualRightBoundaryEdge_mem_dualCutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectDualRightBoundaryEdge_mem_dualCutEdges_eq
  {R : FKRectTorus}
  {y : Fin R.height} :
-- imply
  fkRectDualRightBoundaryEdge R y ∈ fkRectDualCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectDualRightBoundaryEdge_mem_dualCutEdges R y

/--
[mem_fkRectDualRightBoundaryEdgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma mem_fkRectDualRightBoundaryEdgeList_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  e ∈ fkRectDualRightBoundaryEdgeList R ↔ ∃ y : Fin R.height, fkRectDualRightBoundaryEdge R y = e := by
-- proof
  apply StatMech.FrontierD.mem_fkRectDualRightBoundaryEdgeList R e

/--
[fkRectDualRightBoundaryEdgeList_subset_dualCutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectDualRightBoundaryEdgeList_subset_dualCutEdges_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
-- given
  (he : e ∈ fkRectDualRightBoundaryEdgeList R) :
-- imply
  e ∈ fkRectDualCutEdges R := by
-- proof
  apply StatMech.FrontierD.fkRectDualRightBoundaryEdgeList_subset_dualCutEdges R he

/--
[mem_fkRectWiredDualRightBoundaryAddedEdgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma mem_fkRectWiredDualRightBoundaryAddedEdgeList_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  e ∈ fkRectWiredDualRightBoundaryAddedEdgeList R omega ↔ e ∈ fkRectDualRightBoundaryEdgeList R ∧ e ∈ fkRectWiredDualAddedEdges R omega := by
-- proof
  apply StatMech.FrontierD.mem_fkRectWiredDualRightBoundaryAddedEdgeList R omega e

/--
[mem_fkRectZeroTurnDualRightBoundaryContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnDualRightBoundaryContacts_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {y : Fin R.height} :
-- imply
  y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ↔ (fkRectRightColumn R, y) ∈ (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C).support := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnDualRightBoundaryContacts R omega C y

/--
[fkRectZeroTurnDualRightBoundaryContacts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectZeroTurnDualRightBoundaryContacts_nonempty_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  (fkRectZeroTurnDualRightBoundaryContacts R omega C).Nonempty := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnDualRightBoundaryContacts_nonempty R omega C

/--
[fkRectBlackBoundaryPerm_insert_merge_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPerm_insert_merge_partition_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {x : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hmerge : ¬ (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F)))).SameCycle (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ↔ (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ∨ (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) x := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPerm_insert_merge_partition R F e heF hmerge x

/--
[fkRectBlackBoundaryPerm_sameCycle_insertEdgeList_of_mergeOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPerm_sameCycle_insertEdgeList_of_mergeOrder_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {es : List R.EdgeIndex}
  {x y : FKMedialBlackDart R.medialTorus}
-- given
  (horder : FKRectMergeInsertionOrder R F es)
  (hxy : (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).SameCycle x y) :
-- imply
  (fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (fkRectInsertEdgeList R F es)))).SameCycle x y := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPerm_sameCycle_insertEdgeList_of_mergeOrder R F es horder hxy

/--
[fkRectMedialLoopGraph_reachable_insertEdgeList_of_mergeOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean)
-/
@[path]
private lemma fkRectMedialLoopGraph_reachable_insertEdgeList_of_mergeOrder_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {es : List R.EdgeIndex}
  {d e : FKMedialDart R.medialTorus}
-- given
  (horder : FKRectMergeInsertionOrder R F es)
  (hde : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable d e) :
-- imply
  (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (fkRectInsertEdgeList R F es)))).Reachable d e := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopGraph_reachable_insertEdgeList_of_mergeOrder R F es horder hde


-- created on 2026-10-23
