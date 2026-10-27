import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy.Part6
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectGraphConfigurationExtend_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_setOpen_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphConfigurationExtend R (setOpen e eta) = setOpen e.1 (fkRectGraphConfigurationExtend R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_setOpen R e eta

/--
[fkRectGraphConfigurationExtend_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphConfigurationExtend_setClosed_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphConfigurationExtend R (setClosed e eta) = setClosed e.1 (fkRectGraphConfigurationExtend R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphConfigurationExtend_setClosed R e eta

/--
[fkRectGraphCriticalProb_setClosed_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalProb_setClosed_ge_eq
  {R : FKRectTorus}
  {q : Real}
  {eta : FKRectGraphConfiguration R}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q * (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) + fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) ≤ fkRectGraphCriticalRandomClusterProb R q (setClosed e eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalProb_setClosed_ge R hq e eta

/--
[fkRectGraphCriticalProb_setOpen_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalProb_setOpen_ge_eq
  {R : FKRectTorus}
  {q : Real}
  {eta : FKRectGraphConfiguration R}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q * (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) + fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) ≤ fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalProb_setOpen_ge R hq e eta

/--
[fkRectGraphCriticalClosedMass_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalClosedMass_empty_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  fkRectGraphCriticalClosedMass R q ∅ = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalClosedMass_empty R hq

/--
[fkRectGraphCriticalClosedMass_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalClosedMass_reindex_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (he : e ∉ I) :
-- imply
  fkRectGraphCriticalClosedMass R q I = ∑ eta ∈ fkRectGraphClosedFibre R e I, (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) + fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalClosedMass_reindex R q e he

/--
[fkRectGraphCriticalClosedMass_insert_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalClosedMass_insert_reindex_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphCriticalClosedMass R q (insert e I) = ∑ eta ∈ fkRectGraphClosedFibre R e I, fkRectGraphCriticalRandomClusterProb R q (setClosed e eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalClosedMass_insert_reindex R q e I

/--
[fkRectGraphCritical_cFE_mul_closedMass_le_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_mul_closedMass_le_insert_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (he : e ∉ I) :
-- imply
  FK.cFE (fkRectCriticalP q) q * fkRectGraphCriticalClosedMass R q I ≤ fkRectGraphCriticalClosedMass R q (insert e I) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_mul_closedMass_le_insert R hq e he

/--
[fkRectGraphCritical_cFE_pow_le_closedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_pow_le_closedMass_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card ≤ fkRectGraphCriticalClosedMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_pow_le_closedMass R hq I

/--
[fkRectGraphCriticalOpenMass_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalOpenMass_eq_expectation_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphCriticalOpenMass R q I = ∑ eta, fkRectGraphCriticalRandomClusterProb R q eta * fkRectGraphOpenIndicator R I eta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalOpenMass_eq_expectation R q I

/--
[monotone_fkRectGraphOpenIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma monotone_fkRectGraphOpenIndicator_eq
  {R : FKRectTorus}
-- given
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  Monotone (fkRectGraphOpenIndicator R I) := by
-- proof
  apply StatMech.FrontierD.monotone_fkRectGraphOpenIndicator R I

/--
[fkRectGraphOpenIndicator_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphOpenIndicator_insert_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphOpenIndicator R (insert e I) eta = fkRectGraphOpenIndicator R {e} eta * fkRectGraphOpenIndicator R I eta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphOpenIndicator_insert R e I eta

/--
[fkRectGraphCriticalOpenMass_singleton_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalOpenMass_singleton_reindex_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphCriticalOpenMass R q {e} = ∑ eta ∈ fkRectGraphClosedFibre R e ∅, fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalOpenMass_singleton_reindex R q e

/--
[fkRectGraphCritical_cFE_le_openMass_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_le_openMass_singleton_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q ≤ fkRectGraphCriticalOpenMass R q {e} := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_le_openMass_singleton R hq e

/--
[fkRectGraphCriticalOpenMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalOpenMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q)
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  0 ≤ fkRectGraphCriticalOpenMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalOpenMass_nonneg R hq I

/--
[fkRectGraphCritical_cFE_mul_openMass_le_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_mul_openMass_le_insert_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q * fkRectGraphCriticalOpenMass R q I ≤ fkRectGraphCriticalOpenMass R q (insert e I) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_mul_openMass_le_insert R hq e I

/--
[fkRectGraphCritical_cFE_pow_le_openMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_pow_le_openMass_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card ≤ fkRectGraphCriticalOpenMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_pow_le_openMass R hq I

/--
[fkRectGraphCriticalClosedMass_map_edgeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalClosedMass_map_edgeEquiv_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex} :
-- imply
  fkRectGraphCriticalClosedMass R q (I.map (fkRectEdgeGraphEquiv R).toEmbedding) = fkRectCriticalClosedMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalClosedMass_map_edgeEquiv R q I

/--
[fkRectCritical_cFE_pow_le_closedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_le_closedMass_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card ≤ fkRectCriticalClosedMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_le_closedMass R hq I

/--
[fkRectGraphCriticalOpenMass_map_edgeEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectGraphCriticalOpenMass_map_edgeEquiv_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex} :
-- imply
  fkRectGraphCriticalOpenMass R q (I.map (fkRectEdgeGraphEquiv R).toEmbedding) = fkRectCriticalOpenMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalOpenMass_map_edgeEquiv R q I

/--
[fkRectCritical_cFE_pow_le_openMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_le_openMass_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card ≤ fkRectCriticalOpenMass R q I := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_le_openMass R hq I


-- created on 2026-10-23
