/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnalyticCandidateSheet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticStabilitySheet
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexCoordinateBetheWave_branch
    {N n : Nat} (p : Real → Fin n → Real) (hp : Continuous p) :
    Continuous (fun c => sixVertexCoordinateBetheWave (N := N) c (p c)) := by
  rw [continuous_pi_iff]
  intro x
  unfold sixVertexCoordinateBetheWave sixVertexBetheAmplitude
    sixVertexBethePairProduct sixVertexBetheMonomial
    sixVertexBethePairFactor sixVertexBethePhase sixVertexDelta
  fun_prop


theorem sixVertexBetheEigenvalueCandidate_evenSymmetricLift
    {m : Nat} (c : Real) (q : Fin m → Real) :
    sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) =
      sixVertexSymmetricBetheEigenvalueCandidate c q := by
  unfold sixVertexBetheEigenvalueCandidate
    sixVertexSymmetricBetheEigenvalueCandidate
  have hprod (f : Real → Complex) :
      (∏ i, f (sixVertexEvenSymmetricLift m q i)) =
        (∏ j, f (q j)) * ∏ j, f (-q j) := by
    rw [Fin.prod_univ_add]
    simp_rw [sixVertexEvenSymmetricLift_castAdd,
      sixVertexEvenSymmetricLift_natAdd]
    have hrev : (∏ x : Fin m, f (-q x.rev)) = ∏ x, f (-q x) := by
      simpa using (Equiv.prod_comp Fin.revPerm (fun x => f (-q x)))
    rw [hrev, mul_comm]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [hprod (fun r => sixVertexBetheL c (sixVertexBethePhase r)),
    hprod (fun r => sixVertexBetheM c (sixVertexBethePhase r))]


theorem sixVertexBetheEigenvalueCandidate_evenSymmetricLift_eq_value
    {m : Nat} (c : Real) (q : Fin m → Real) :
    sixVertexBetheEigenvalueCandidate c (sixVertexEvenSymmetricLift m q) =
      (sixVertexSymmetricBetheEigenvalueValue c q : Complex) := by
  rw [sixVertexBetheEigenvalueCandidate_evenSymmetricLift,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]


end
end StatMech.FrontierD
