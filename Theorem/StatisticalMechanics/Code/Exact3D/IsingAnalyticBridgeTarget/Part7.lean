/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem hasCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (T.correlationLength β) := by
  have hξ :
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.mass β)⁻¹ :=
    (T.mass_realizes_inverse_length β hβ).hasCorrelationLength_inv
      (T.mass_pos β hβ)
  simpa [T.correlationLength_eq_inv_mass β hβ] using hξ


theorem hasInverseCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin
      ising3DXAxisRay (T.mass β) :=
  T.mass_realizes_inverse_length β hβ


theorem eventually_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3) :=
  eventually_mem_isingLeftCriticalIoo T.δ_pos


theorem betaC_sub_pos_of_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem betaC_sub_lt_delta_of_mem_leftCriticalInterval
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < T.δ :=
  betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β :=
  eventually_betaC_sub_pos_isingLeftCriticalIoo T.δ_pos


theorem eventually_betaC_sub_lt_delta
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < T.δ :=
  eventually_betaC_sub_lt_delta_isingLeftCriticalIoo T.δ_pos


theorem eventually_mass_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.mass β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_pos β hβ


theorem eventually_hasInverseCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (T.mass β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasInverseCorrelationLength hβ


theorem eventually_correlationLength_eq_inv_mass
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β = (T.mass β)⁻¹ := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.correlationLength_eq_inv_mass β hβ


theorem eventually_hasCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (T.correlationLength β) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.hasCorrelationLength hβ


theorem eventually_massPrefactor_pos
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < T.massPrefactor β := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.massPrefactor_pos β hβ


theorem eventually_mass_scaling
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.mass β =
        T.massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  filter_upwards [T.eventually_mem_leftCriticalInterval] with β hβ
  exact T.mass_scaling β hβ


theorem lengthScalingFromMass
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    {β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - T.δ) (Ising.betaC 3)) :
    T.correlationLength β =
      (T.massPrefactor β)⁻¹ *
        Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
  rw [T.correlationLength_eq_inv_mass β hβ, T.mass_scaling β hβ]
  have hBne : T.massPrefactor β ≠ 0 := (T.massPrefactor_pos β hβ).ne'
  have hexpne :
      Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) ≠ 0 :=
    Real.exp_ne_zero _
  rw [show -C.predictedExponent * Real.log (Ising.betaC 3 - β) =
      -(C.predictedExponent * Real.log (Ising.betaC 3 - β)) by ring,
    Real.exp_neg]
  field_simp [hBne, hexpne]


end IsingMassPowerLawAnalyticRGToExponentTarget
end Exact3D
end StatMech
