/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexBetheEigenvalueCandidate c
        (sixVertexFixedChargeBetheRoots hc (2 * s) k) =
      (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) := by
  rw [sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric hc s k,
    sixVertexSymmetricBetheEigenvalueCandidate_eq_value]
  rfl

theorem sixVertexFixedEvenChargeBetheEigenvalueValue_pos
    {c : Real} (hc : 2 < c) (s k : Nat) :
    0 < sixVertexFixedEvenChargeBetheEigenvalueValue hc s k := by
  exact sixVertexSymmetricBetheEigenvalueValue_pos hc _


theorem sixVertexFixedEvenChargeBetheRoots_eigenrelation_value
    {c : Real} (hc : 2 < c) (s k : Nat) :
    (sixVertexSectorTransferComplex (sixVertexFourWidth (2 * s) k)
        (sixVertexFixedChargeBetheParticleCount (2 * s) k) c).mulVec
        (sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k)) =
      (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) •
        sixVertexCoordinateBetheWave c
          (sixVertexFixedChargeBetheRoots hc (2 * s) k) := by
  have h := sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge
    hc (r := 2 * s) ⟨s, by omega⟩ k
  unfold SixVertexCoordinateBetheEigenrelation at h
  rwa [sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value hc s k] at h

theorem sixVertexFixedEvenChargeBetheEigenvalueValue_log
    {c : Real} (hc : 2 < c) (s k : Nat) :
    Real.log (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k) =
      Real.log 2 + 2 * ∑ j,
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖ := by
  exact sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc _


end
end StatMech.FrontierD
