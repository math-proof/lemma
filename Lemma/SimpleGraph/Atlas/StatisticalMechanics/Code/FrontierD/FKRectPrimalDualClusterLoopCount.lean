import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualClusterLoopCount
open StatMech StatMech.FrontierD


/--
[fkRectOpenEdgeCount_add_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualClusterLoopCount.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_add_dual_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R omega + fkRectOpenEdgeCount R (fkRectDualConfigurationEquiv R omega) = Fintype.card R.EdgeIndex := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_add_dual R omega

/--
[fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualClusterLoopCount.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectMedialLoopCount R omega + fkRectNetIndicator R omega + fkRectNetIndicator R (fkRectDualConfigurationEquiv R omega) = fkRectNumClusters R omega + fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_add_netIndicators_eq_clusterCounts R omega

/--
[fkRectMedialLoopCount_eq_clusterCounts_or_pred_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualClusterLoopCount.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_eq_clusterCounts_or_pred_of_not_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hnoNet : ¬ FKRectHasNet R omega) :
-- imply
  fkRectMedialLoopCount R omega = fkRectNumClusters R omega + fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) ∨ fkRectMedialLoopCount R omega + 1 = fkRectNumClusters R omega + fkRectNumClusters R (fkRectDualConfigurationEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_eq_clusterCounts_or_pred_of_not_hasNet R omega hnoNet


-- created on 2026-10-23
