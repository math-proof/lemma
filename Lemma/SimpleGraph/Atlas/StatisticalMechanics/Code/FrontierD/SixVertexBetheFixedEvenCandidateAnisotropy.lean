import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedEvenPositiveBetheRootAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedEvenPositiveBetheRootAt_eq_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexFixedEvenPositiveBetheRootAt s k j c = sixVertexFixedEvenPositiveBetheRoots hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenPositiveBetheRootAt_eq hc s k j

/--
[tendsto_sixVertexFixedEvenPositiveBetheRootAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedEvenPositiveBetheRootAt_eq
  {s k : Nat}
  {j : Fin (s + k + 1)} :
-- imply
  Tendsto (sixVertexFixedEvenPositiveBetheRootAt s k j) atTop (nhds (sixVertexFixedEvenPositiveLimitingRoot s k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedEvenPositiveBetheRootAt s k j

/--
[sixVertexFixedEvenPositiveLimitingRoot_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedEvenPositiveLimitingRoot_pos_eq
  {s k : Nat}
  {j : Fin (s + k + 1)} :
-- imply
  0 < sixVertexFixedEvenPositiveLimitingRoot s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenPositiveLimitingRoot_pos s k j

/--
[sixVertexFixedEvenPositiveLimitingPhase_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma sixVertexFixedEvenPositiveLimitingPhase_ne_one_eq
  {s k : Nat}
  {j : Fin (s + k + 1)} :
-- imply
  sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenPositiveLimitingPhase_ne_one s k j

/--
[tendsto_sixVertexFixedChargeBetheM_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeBetheM_normalized_eq
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hphase : sixVertexFixedChargeLimitingPhase r k j ≠ 1) :
-- imply
  Tendsto (fun c => sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) / (c ^ 2 - 2 : Real)) atTop (nhds (-1 / (1 - sixVertexFixedChargeLimitingPhase r k j))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeBetheM_normalized r k j hphase

/--
[tendsto_sixVertexFixedEvenPositiveBetheM_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedEvenPositiveBetheM_normalized_eq
  {s k : Nat}
  {j : Fin (s + k + 1)} :
-- imply
  Tendsto (fun c => sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedEvenPositiveBetheRootAt s k j c)) / (c ^ 2 - 2 : Real)) atTop (nhds (-1 / (1 - sixVertexBethePhase (sixVertexFixedEvenPositiveLimitingRoot s k j)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedEvenPositiveBetheM_normalized s k j

/--
[tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized_eq
  {s k : Nat}
  {j : Fin (s + k + 1)} :
-- imply
  Tendsto (fun c => Complex.normSq (sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedEvenPositiveBetheRootAt s k j c)) / (c ^ 2 - 2 : Real))) atTop (nhds (sixVertexFixedEvenPositiveLimitingMNormSq s k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedEvenPositiveBetheM_normSq_normalized s k j

/--
[tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized_eq
  {s k : Nat} :
-- imply
  Tendsto (sixVertexFixedEvenChargeBetheCandidateNormalized s k) atTop (nhds (sixVertexFixedEvenChargeBetheCandidateInfinity s k)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedEvenChargeBetheCandidateNormalized s k


-- created on 2026-10-23
