import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkRectTorusGraph_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma mem_fkRectTorusGraph_edgeSet_iff_eq
  {R : FKRectTorus}
  {e : Sym2 R.Vertex} :
-- imply
  e ∈ (fkRectTorusGraph R).edgeSet ↔ ∃ a : R.EdgeIndex, fkRectTorusIndexedEdge R a = e := by
-- proof
  apply StatMech.FrontierD.mem_fkRectTorusGraph_edgeSet_iff R e

/--
[fkRectEdgeToGraphEdge_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectEdgeToGraphEdge_bijective_eq
  {R : FKRectTorus} :
-- imply
  Function.Bijective (fkRectEdgeToGraphEdge R) := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeToGraphEdge_bijective R

/--
[fkRectEdgeGraphEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectEdgeGraphEquiv_val_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  (fkRectEdgeGraphEquiv R a).1 = fkRectTorusIndexedEdge R a := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeGraphEquiv_val R a

/--
[fkRectEdgeGraphEquiv_symm_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectEdgeGraphEquiv_symm_indexedEdge_eq
  {R : FKRectTorus}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectTorusIndexedEdge R ((fkRectEdgeGraphEquiv R).symm e) = e.1 := by
-- proof
  apply StatMech.FrontierD.fkRectEdgeGraphEquiv_symm_indexedEdge R e

/--
[fkRectFullGraphConfiguration_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_indexedEdge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {a : R.EdgeIndex} :
-- imply
  fkRectFullGraphConfiguration R omega (fkRectTorusIndexedEdge R a) = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_indexedEdge R omega a

/--
[fkRectFullGraphConfiguration_eq_false_of_not_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_eq_false_of_not_edge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : Sym2 R.Vertex}
-- given
  (he : e ∉ (fkRectTorusGraph R).edgeSet) :
-- imply
  fkRectFullGraphConfiguration R omega e = false := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_eq_false_of_not_edge R omega he

/--
[fkOpenSub_fullGraphConfiguration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkOpenSub_fullGraphConfiguration_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  StatMech.FK.openSub (fkRectTorusGraph R) (fkRectFullGraphConfiguration R omega) = fkRectOpenGraph R omega := by
-- proof
  apply StatMech.FrontierD.fkOpenSub_fullGraphConfiguration R omega

/--
[fkRectConfigurationGraphEquiv_apply_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectConfigurationGraphEquiv_apply_edge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {a : R.EdgeIndex} :
-- imply
  fkRectConfigurationGraphEquiv R omega (fkRectEdgeGraphEquiv R a) = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationGraphEquiv_apply_edge R omega a

/--
[fkRectGraphOpenGraph_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraphOpenGraph_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectGraphOpenGraph R (fkRectConfigurationGraphEquiv R omega) = fkRectOpenGraph R omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraphOpenGraph_configurationGraphEquiv R omega

/--
[fkRectGraph_clusterCount_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraph_clusterCount_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Fintype.card (fkRectGraphOpenGraph R (fkRectConfigurationGraphEquiv R omega)).ConnectedComponent = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraph_clusterCount_configurationGraphEquiv R omega

/--
[fkRectGraphOpenEdgeCount_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraphOpenEdgeCount_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectGraphOpenEdgeCount R (fkRectConfigurationGraphEquiv R omega) = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraphOpenEdgeCount_configurationGraphEquiv R omega

/--
[fkRectGraphCriticalReducedWeight_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraphCriticalReducedWeight_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectGraphCriticalReducedWeight R q (fkRectConfigurationGraphEquiv R omega) = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalReducedWeight_configurationGraphEquiv R q omega

/--
[fkRectGraphCriticalReducedZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraphCriticalReducedZ_eq_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectGraphCriticalReducedZ R q = fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalReducedZ_eq R q

/--
[fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterGraphBridge.lean)
-/
@[path]
private lemma fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectGraphCriticalRandomClusterProb R q (fkRectConfigurationGraphEquiv R omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalRandomClusterProb_configurationGraphEquiv R q omega


-- created on 2026-10-23
