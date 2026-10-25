import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectGraphForceClosed_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceClosed_of_mem_eq
  {R : FKRectTorus}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
  {eta : FKRectGraphConfiguration R}
  {e}
-- given
  (he : e ∈ I) :
-- imply
  fkRectGraphForceClosed R I eta e = false := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceClosed_of_mem R eta he

/--
[fkRectGraphForceClosed_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceClosed_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
  {eta : FKRectGraphConfiguration R}
  {e}
-- given
  (he : e ∉ I) :
-- imply
  fkRectGraphForceClosed R I eta e = eta e := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceClosed_of_not_mem R eta he

/--
[fkRectGraphForceClosed_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceClosed_empty_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R} :
-- imply
  fkRectGraphForceClosed R ∅ eta = eta := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceClosed_empty R eta

/--
[fkRectGraphForceClosed_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceClosed_insert_eq
  {R : FKRectTorus}
  {eta : FKRectGraphConfiguration R}
-- given
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  fkRectGraphForceClosed R (insert e I) eta = fkRectGraphForceClosed R I (setClosed e eta) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceClosed_insert R I e eta

/--
[fkRectGraphCriticalEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphCriticalEventMass_mono_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set (FKRectGraphConfiguration R)}
-- given
  (hq : 0 < q)
  (hAB : A ⊆ B) :
-- imply
  fkRectGraphCriticalEventMass R q A ≤ fkRectGraphCriticalEventMass R q B := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalEventMass_mono R hq hAB

/--
[fkRectGraphCritical_cFE_mul_preimage_setClosed_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_mul_preimage_setClosed_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set (FKRectGraphConfiguration R)}
-- given
  (hq : 1 ≤ q)
  (e : {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q * fkRectGraphCriticalEventMass R q (setClosed e ⁻¹' A) ≤ fkRectGraphCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_mul_preimage_setClosed_le_event R hq e A

/--
[fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set (FKRectGraphConfiguration R)}
-- given
  (hq : 1 ≤ q)
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectGraphCriticalEventMass R q (fkRectGraphForceClosed R I ⁻¹' A) ≤ fkRectGraphCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_pow_mul_forceClosed_preimage_le_event R hq I A

/--
[fkRectGraphForceOpen_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceOpen_of_mem_eq
  {R : FKRectTorus}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
  {eta : FKRectGraphConfiguration R}
  {e}
-- given
  (he : e ∈ I) :
-- imply
  fkRectGraphForceOpen R I eta e = true := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceOpen_of_mem R eta he

/--
[fkRectGraphForceOpen_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphForceOpen_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
  {eta : FKRectGraphConfiguration R}
  {e}
-- given
  (he : e ∉ I) :
-- imply
  fkRectGraphForceOpen R I eta e = eta e := by
-- proof
  apply StatMech.FrontierD.fkRectGraphForceOpen_of_not_mem R eta he

/--
[fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set (FKRectGraphConfiguration R)}
-- given
  (hq : 1 ≤ q)
  (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectGraphCriticalEventMass R q (fkRectGraphForceOpen R I ⁻¹' A) ≤ fkRectGraphCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event R hq I A

/--
[fkRectForceEdgesClosed_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectForceEdgesClosed_of_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ I) :
-- imply
  fkRectForceEdgesClosed R I omega a = false := by
-- proof
  apply StatMech.FrontierD.fkRectForceEdgesClosed_of_mem R omega ha

/--
[fkRectForceEdgesClosed_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectForceEdgesClosed_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ I) :
-- imply
  fkRectForceEdgesClosed R I omega a = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectForceEdgesClosed_of_not_mem R omega ha

/--
[fkRectForceEdgesOpen_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectForceEdgesOpen_of_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ I) :
-- imply
  fkRectForceEdgesOpen R I omega a = true := by
-- proof
  apply StatMech.FrontierD.fkRectForceEdgesOpen_of_mem R omega ha

/--
[fkRectForceEdgesOpen_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectForceEdgesOpen_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ I) :
-- imply
  fkRectForceEdgesOpen R I omega a = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectForceEdgesOpen_of_not_mem R omega ha

/--
[mem_fkRectGraphEdgesOfIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma mem_fkRectGraphEdgesOfIndices_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {a : R.EdgeIndex} :
-- imply
  fkRectEdgeGraphEquiv R a ∈ fkRectGraphEdgesOfIndices R I ↔ a ∈ I := by
-- proof
  apply StatMech.FrontierD.mem_fkRectGraphEdgesOfIndices R I a

/--
[fkRectGraphEdgesOfIndices_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphEdgesOfIndices_card_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex} :
-- imply
  (fkRectGraphEdgesOfIndices R I).card = I.card := by
-- proof
  apply StatMech.FrontierD.fkRectGraphEdgesOfIndices_card R I

/--
[fkRectConfigurationGraphEquiv_forceEdgesClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectConfigurationGraphEquiv_forceEdgesClosed_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration} :
-- imply
  fkRectConfigurationGraphEquiv R (fkRectForceEdgesClosed R I omega) = fkRectGraphForceClosed R (fkRectGraphEdgesOfIndices R I) (fkRectConfigurationGraphEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationGraphEquiv_forceEdgesClosed R I omega

/--
[fkRectConfigurationGraphEquiv_forceEdgesOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectConfigurationGraphEquiv_forceEdgesOpen_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {omega : R.Configuration} :
-- imply
  fkRectConfigurationGraphEquiv R (fkRectForceEdgesOpen R I omega) = fkRectGraphForceOpen R (fkRectGraphEdgesOfIndices R I) (fkRectConfigurationGraphEquiv R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationGraphEquiv_forceEdgesOpen R I omega

/--
[fkRectCriticalEventMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_nonneg R hq A

/--
[fkRectCriticalEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_mono_eq
  {R : FKRectTorus}
  {q : Real}
  {A B : Set R.Configuration}
-- given
  (hq : 0 < q)
  (hAB : A ⊆ B) :
-- imply
  fkRectCriticalEventMass R q A ≤ fkRectCriticalEventMass R q B := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_mono R hq hAB

/--
[fkRectCriticalEventMass_cutClosed_eq_closedMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_cutClosed_eq_closedMass_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta} = fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_cutClosed_eq_closedMass R q

/--
[fkRectCriticalClosedMass_cut_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalClosedMass_cut_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  0 < fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalClosedMass_cut_pos R hq

/--
[closedMass_mul_fkRectCriticalCutFreeEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma closedMass_mul_fkRectCriticalCutFreeEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) * fkRectCriticalCutFreeEventMass R q A = fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ eta ∈ A} := by
-- proof
  apply StatMech.FrontierD.closedMass_mul_fkRectCriticalCutFreeEventMass R hq A

/--
[fkRectCriticalCutFreeEventMass_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalCutFreeEventMass_univ_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalCutFreeEventMass R q Set.univ = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalCutFreeEventMass_univ R hq

/--
[fkRectGraphCriticalEventMass_eq_indexed_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectGraphCriticalEventMass_eq_indexed_preimage_eq
  {R : FKRectTorus}
  {q : Real}
  {B : Set (FKRectGraphConfiguration R)} :
-- imply
  fkRectGraphCriticalEventMass R q B = fkRectCriticalEventMass R q (fkRectConfigurationGraphEquiv R ⁻¹' B) := by
-- proof
  apply StatMech.FrontierD.fkRectGraphCriticalEventMass_eq_indexed_preimage R q B

/--
[fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q (fkRectForceEdgesClosed R I ⁻¹' A) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_forceEdgesClosed_preimage_le_event R hq I A

/--
[fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q (fkRectForceEdgesOpen R I ⁻¹' A) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_forceEdgesOpen_preimage_le_event R hq I A

/--
[fkRectForceEdgesClosed_torusCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectForceEdgesClosed_torusCut_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectForceEdgesClosed R (fkRectTorusCutEdges R) omega = fkRectForceCutClosed R omega := by
-- proof
  apply StatMech.FrontierD.fkRectForceEdgesClosed_torusCut R omega

/--
[fkRectCritical_cutPushforward_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_cutPushforward_event_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) * fkRectCriticalEventMass R q (fkRectForceCutClosed R ⁻¹' A) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cutPushforward_event R hq A

/--
[fkRectCriticalZeroTurnAboveMass_eq_eventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnAboveMass_eq_eventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat} :
-- imply
  fkRectCriticalZeroTurnAboveMass R q L = fkRectCriticalEventMass R q {omega | L < fkRectZeroTurnLoopCount R omega} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnAboveMass_eq_eventMass R q L

/--
[fkRectCritical_zeroTurnAbove_cut_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_cut_transfer_eq
  {R : FKRectTorus}
  {q : Real}
  {K : R.Configuration → Nat}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (htop : ∀ omega : R.Configuration, fkRectZeroTurnLoopCount R omega ≤ 2 * R.width + K (fkRectForceCutClosed R omega)) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) * fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) ≤ fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < K eta} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_cut_transfer R hq K htop n


-- created on 2026-10-23
