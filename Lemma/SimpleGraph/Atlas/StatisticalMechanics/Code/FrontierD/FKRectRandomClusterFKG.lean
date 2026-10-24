import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectGraphConfigurationExtend_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_edge_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphConfigurationExtend R eta e.1 = eta e := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_edge R eta e

/--
[fk_openSub_configurationExtend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fk_openSub_configurationExtend_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R} :
-- imply
  FK.openSub (fkRectTorusGraph R) (fkRectGraphConfigurationExtend R eta) = fkRectGraphOpenGraph R eta := by
-- proof
  apply StatMech.FrontierD.fk_openSub_configurationExtend R eta

/--
[fk_numClusters_configurationExtend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fk_numClusters_configurationExtend_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R} :
-- imply
  FK.numClusters (fkRectTorusGraph R) (fkRectGraphConfigurationExtend R eta) = Fintype.card (fkRectGraphOpenGraph R eta).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.fk_numClusters_configurationExtend R eta

/--
[fk_edgeProduct_configurationExtend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fk_edgeProduct_configurationExtend_eq
  {R : FKRectTorus}
  {p : Real}
  {eta : FKRectGraphConfiguration R} :
-- imply
  FK.edgeProduct (fkRectTorusGraph R) p (fkRectGraphConfigurationExtend R eta) = ∏ e : {e // e ∈ (fkRectTorusGraph R).edgeSet}, if eta e then p else 1 - p := by
-- proof
  apply StatMech.FrontierD.fk_edgeProduct_configurationExtend R p eta

/--
[fk_edgeProduct_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fk_edgeProduct_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {p : Real}
  {omega : R.Configuration} :
-- imply
  FK.edgeProduct (fkRectTorusGraph R) p (fkRectGraphConfigurationExtend R (fkRectConfigurationGraphEquiv R omega)) = fkRectEdgeProduct R p omega := by
-- proof
  apply StatMech.FrontierD.fk_edgeProduct_configurationGraphEquiv R p omega

/--
[fkWeight_configurationGraphEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkWeight_configurationGraphEquiv_eq
  {R : FKRectTorus}
  {p q : Real}
  {omega : R.Configuration} :
-- imply
  FK.fkWeight (fkRectTorusGraph R) p q (fkRectGraphConfigurationExtend R (fkRectConfigurationGraphEquiv R omega)) = fkRectRandomClusterWeight R p q omega := by
-- proof
  apply StatMech.FrontierD.fkWeight_configurationGraphEquiv R p q omega

/--
[fkRectGraphConfigurationExtend_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_sup_eq
  {R : FKRectTorus}
  {eta zeta : FKRectGraphConfiguration R} :
-- imply
  fkRectGraphConfigurationExtend R (eta ⊔ zeta) = fkRectGraphConfigurationExtend R eta ⊔ fkRectGraphConfigurationExtend R zeta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_sup R eta zeta

/--
[fkRectGraphConfigurationExtend_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_inf_eq
  {R : FKRectTorus}
  {eta zeta : FKRectGraphConfiguration R} :
-- imply
  fkRectGraphConfigurationExtend R (eta ⊓ zeta) = fkRectGraphConfigurationExtend R eta ⊓ fkRectGraphConfigurationExtend R zeta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_inf R eta zeta

/--
[fkRectCriticalEdgeFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectCriticalEdgeFactor_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalEdgeFactor R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEdgeFactor_pos R hq

/--
[fkWeight_configurationExtend_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkWeight_configurationExtend_critical_eq
  {R : FKRectTorus}
  {q : Real}
  {eta : FKRectGraphConfiguration R}
-- given
  (hq : 0 < q) :
-- imply
  FK.fkWeight (fkRectTorusGraph R) (fkRectCriticalP q) q (fkRectGraphConfigurationExtend R eta) = fkRectCriticalEdgeFactor R q * fkRectGraphCriticalReducedWeight R q eta := by
-- proof
  apply StatMech.FrontierD.fkWeight_configurationExtend_critical R hq eta

/--
[fkRectGraphCriticalReducedWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCriticalReducedWeight_logSupermodular_eq
  {R : FKRectTorus}
  {q : Real}
  {eta zeta : FKRectGraphConfiguration R}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectGraphCriticalReducedWeight R q eta * fkRectGraphCriticalReducedWeight R q zeta ≤ fkRectGraphCriticalReducedWeight R q (eta ⊔ zeta) * fkRectGraphCriticalReducedWeight R q (eta ⊓ zeta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalReducedWeight_logSupermodular R hq eta zeta

/--
[fkRectGraphCriticalReducedWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCriticalReducedWeight_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {eta : FKRectGraphConfiguration R}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectGraphCriticalReducedWeight R q eta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalReducedWeight_pos R hq eta

/--
[fkRectGraphCriticalReducedZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCriticalReducedZ_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectGraphCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalReducedZ_pos R hq

/--
[fkRectGraphCriticalRandomClusterProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCriticalRandomClusterProb_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {eta : FKRectGraphConfiguration R}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectGraphCriticalRandomClusterProb R q eta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalRandomClusterProb_nonneg R hq eta

/--
[sum_fkRectGraphCriticalRandomClusterProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma sum_fkRectGraphCriticalRandomClusterProb_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  ∑ eta : FKRectGraphConfiguration R, fkRectGraphCriticalRandomClusterProb R q eta = 1 := by
-- proof
  apply StatMech.FrontierD.sum_fkRectGraphCriticalRandomClusterProb R hq

/--
[fkRectConfigurationGraphEquiv_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectConfigurationGraphEquiv_inf_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration} :
-- imply
  fkRectConfigurationGraphEquiv R (omega ⊓ tau) = fkRectConfigurationGraphEquiv R omega ⊓ fkRectConfigurationGraphEquiv R tau := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationGraphEquiv_inf R omega tau

/--
[fkRectConfigurationGraphEquiv_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectConfigurationGraphEquiv_sup_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration} :
-- imply
  fkRectConfigurationGraphEquiv R (omega ⊔ tau) = fkRectConfigurationGraphEquiv R omega ⊔ fkRectConfigurationGraphEquiv R tau := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationGraphEquiv_sup R omega tau

/--
[fkRectGraphCriticalRandomClusterProb_fkgLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCriticalRandomClusterProb_fkgLattice_eq
  {R : FKRectTorus}
  {q : Real}
  {eta zeta : FKRectGraphConfiguration R}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectGraphCriticalRandomClusterProb R q eta * fkRectGraphCriticalRandomClusterProb R q zeta ≤ fkRectGraphCriticalRandomClusterProb R q (eta ⊓ zeta) * fkRectGraphCriticalRandomClusterProb R q (eta ⊔ zeta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalRandomClusterProb_fkgLattice R hq eta zeta

/--
[fkRectCriticalRandomClusterProb_fkgLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_fkgLattice_eq
  {R : FKRectTorus}
  {q : Real}
  {omega tau : R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalRandomClusterProb R q omega * fkRectCriticalRandomClusterProb R q tau ≤ fkRectCriticalRandomClusterProb R q (omega ⊓ tau) * fkRectCriticalRandomClusterProb R q (omega ⊔ tau) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_fkgLattice R hq omega tau

/--
[fkRectGraphCritical_positivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectGraphCritical_positivelyAssociated_eq
  {R : FKRectTorus}
  {q : Real}
  {f g : FKRectGraphConfiguration R → Real}
-- given
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * f eta) * (∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * g eta) ≤ ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * (f eta * g eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_positivelyAssociated R hq hf hg

/--
[fkRectCritical_positivelyAssociated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFKG.lean)
-/
@[path]
private lemma fkRectCritical_positivelyAssociated_eq
  {R : FKRectTorus}
  {q : Real}
  {f g : R.Configuration → Real}
-- given
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ omega, fkRectCriticalRandomClusterProb R q omega * f omega) * (∑ omega, fkRectCriticalRandomClusterProb R q omega * g omega) ≤ ∑ omega, fkRectCriticalRandomClusterProb R q omega * (f omega * g omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_positivelyAssociated R hq hf hg


-- created on 2026-10-23
